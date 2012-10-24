#include <llvm/Module.h>
#include <llvm/Instructions.h>
#include <llvm/IntrinsicInst.h>
#include <llvm/Metadata.h>
#include <llvm/Constants.h>
#include <llvm/Pass.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Support/InstIterator.h>
#include <llvm/Support/Debug.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/Transforms/Utils/Local.h>

#include "Annotation.h"

using namespace llvm;


static inline bool needAnnotation(Value *V) {
	if (PointerType *PTy = dyn_cast<PointerType>(V->getType())) {
		Type *Ty = PTy->getElementType();
		return (Ty->isIntegerTy() || isFunctionPointer(Ty));
	}
	return false;
}

std::string getAnnotation(Value *V, Module *M) {
	std::string id;

	if (GlobalVariable *GV = dyn_cast<GlobalVariable>(V))
		id = getVarId(GV);
	else {
		User::op_iterator is, ie; // GEP indices
		Type *PTy = NULL;         // Type of pointer in GEP
		if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
			// GEP instruction
			is = GEP->idx_begin();
			ie = GEP->idx_end() - 1;
			PTy = GEP->getPointerOperandType();
		} else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
			// constant GEP expression
			if (CE->getOpcode() == Instruction::GetElementPtr) {
				is = CE->op_begin() + 1;
				ie = CE->op_end() - 1;
				PTy = CE->getOperand(0)->getType();
			}
		}
		// id is in the form of struct.[name].[offset]
		if (PTy) {
			SmallVector<Value *, 4> Idx(is, ie);
			Type *Ty = GetElementPtrInst::getIndexedType(PTy, Idx);
			ConstantInt *Offset = dyn_cast<ConstantInt>(ie->get());
			if (Offset && isa<StructType>(Ty))
				id = getStructId(Ty, M, Offset->getLimitedValue());
		}
	}

	return id;
}

static bool annotateLoadStore(Instruction *I) {
	std::string Anno;
	LLVMContext &VMCtx = I->getContext();
	Module *M = I->getParent()->getParent()->getParent();

	if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
		llvm::Value *V = LI->getPointerOperand();
		if (needAnnotation(V))
			Anno = getAnnotation(V, M);
	} else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
		Value *V = SI->getPointerOperand();
		if (needAnnotation(V))
			Anno = getAnnotation(V, M);
	}

	if (Anno.empty())
		return false;

	MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, Anno));
	I->setMetadata(MD_ID, MD);
	return true;
}

static bool annotateArguments(Function &F) {
	bool Changed = false;
	LLVMContext &VMCtx = F.getContext();

	// replace integer arguments with function calls
	for (Function::arg_iterator i = F.arg_begin(),
			e = F.arg_end(); i != e; ++i) {
		if (F.isVarArg())
			break;

		Argument *A = &*i;
		IntegerType *Ty = dyn_cast<IntegerType>(A->getType());
		if (A->use_empty() || !Ty)
			continue;

		std::string Name = "kint_arg.i" + Twine(Ty->getBitWidth()).str();
		Function *AF = cast<Function>(
			F.getParent()->getOrInsertFunction(Name, Ty, NULL));
		CallInst *CI = IntrinsicInst::Create(AF, A->getName(), 
			F.getEntryBlock().getFirstInsertionPt());

		MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, getArgId(A)));
		CI->setMetadata(MD_ID, MD);
		A->replaceAllUsesWith(CI);
		Changed = true;
	}
	return Changed;
}

static StringRef extractConstantString(Value *V) {
	if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
		if (CE->isGEPWithNoNotionalOverIndexing())
			if (GlobalVariable *GV = dyn_cast<GlobalVariable>(CE->getOperand(0)))
				if (Constant *C = GV->getInitializer())
					if (ConstantDataSequential *S = 
								dyn_cast<ConstantDataSequential>(C))
						if (S->isCString())
							return S->getAsCString();
	}
	return "";
}

static bool annotateTaintSource(CallInst *CI, 
								SmallPtrSet<Instruction *, 4> &Erase) {
	LLVMContext &VMCtx = CI->getContext();
	Function *F = CI->getParent()->getParent();
	Function *CF = CI->getCalledFunction();
	StringRef Name = CF->getName();

	// linux system call arguemnts are taint
	if (Name.startswith("kint_arg.i") && F->getName().startswith("sys_")) {
		MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, "syscall"));
		CI->setMetadata(MD_TaintSrc, MD);
		return true;
	}
	
	// other taint sources: int __kint_taint(const char *, ...);
	if (Name == "__kint_taint") {
		// the 1st arg is the description
		StringRef Desc = extractConstantString(CI->getArgOperand(0));
		// the 2nd arg and return value are tainted
		MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, Desc));
		if (Instruction *I = dyn_cast_or_null<Instruction>(CI->getArgOperand(1)))
			I->setMetadata(MD_TaintSrc, MD);
		if (!CI->use_empty())
			CI->setMetadata(MD_TaintSrc, MD);
		else
			Erase.insert(CI);
		return true;
	}
	return false;
}

static bool annotateSink(CallInst *CI) {
	#define P std::make_pair
	static std::pair<const char *, int> Allocs[] = {
		P("dma_alloc_from_coherent", 1),
		P("__kmalloc", 0),
		P("kmalloc", 0),
		P("__kmalloc_node", 0),
		P("kmalloc_node", 0),
		P("kzalloc", 0),
		P("kcalloc", 0),
		P("kcalloc", 1),
		P("kmemdup", 1),
		P("memdup_user", 1),
		P("pci_alloc_consistent", 1),
		P("__vmalloc", 0),
		P("vmalloc", 0),
		P("vmalloc_user", 0),
		P("vmalloc_node", 0),
		P("vzalloc", 0),
		P("vzalloc_node", 0),
	};
	#undef P

	LLVMContext &VMCtx = CI->getContext();
	StringRef Name = CI->getCalledFunction()->getName();

	for (unsigned i = 0; i < sizeof(Allocs) / sizeof(Allocs[0]); ++i) {
		if (Name == Allocs[i].first) {
			Value *V = CI->getArgOperand(Allocs[i].second);
			if (Instruction *I = dyn_cast_or_null<Instruction>(V)) {
				MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, Name));
				I->setMetadata(MD_Sink, MD);
				return true;
			}
		}
	}
	return false;
}


bool AnnotationPass::runOnFunction(Function &F) {
	bool Changed = false;

	Changed |= annotateArguments(F);

	SmallPtrSet<Instruction *, 4> EraseSet;
	for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
		Instruction *I = &*i;

		if (isa<LoadInst>(I) || isa<StoreInst>(I)) {
			Changed |= annotateLoadStore(I);
		} else if (CallInst *CI = dyn_cast<CallInst>(I)) {
			if (!CI->getCalledFunction())
				continue;
			Changed |= annotateTaintSource(CI, EraseSet);
			Changed |= annotateSink(CI);
		}
	}
	for (SmallPtrSet<Instruction *, 4>::iterator i = EraseSet.begin(),
			e = EraseSet.end(); i != e; ++i) {
		(*i)->eraseFromParent();
	}
	return Changed;
}

bool AnnotationPass::doInitialization(Module &M)
{
	this->M = &M;
	return true;
}


char AnnotationPass::ID;

static RegisterPass<AnnotationPass>
X("anno", "add id annotation for load/stores; add taint annotation for calls");


