#include <llvm/DebugInfo.h>
#include <llvm/Module.h>
#include <llvm/Pass.h>
#include <llvm/Constants.h>
#include <llvm/Instructions.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/InstIterator.h>
#include <llvm/Analysis/CallGraph.h>

#include "Annotation.h"
#include "IntGlobal.h"

using namespace llvm;

// Check both local taint and global sources
bool TaintPass::isTaint(Value *V)
{
	if (VTS.count(V) || VTS.count(V->stripPointerCasts()))
		return true;
	
	// if not in VTS, check external taint
	if (CallInst *CI = dyn_cast<CallInst>(V)) {
		// taint if any possible callee could return taint
		if (!CI->isInlineAsm() && Ctx->Callees.count(CI)) {
			FuncSet &CEEs = Ctx->Callees[CI];
			for (FuncSet::iterator i = CEEs.begin(), e = CEEs.end();
				 i != e; ++i) {
				if (Ctx->Taints.count(getRetId(*i))) {
					VTS.insert(CI);
					return true;
				}
			}
		}
	} else {
		// arguments and loads
		std::string sID = getValueId(V);
		if (sID != "" && (Ctx->Taints.count(sID))) {
			VTS.insert(V);
			return true;
		}
	}
	return false;
}

bool TaintPass::isTaintSource(const std::string &sID)
{
	TaintSet::iterator it = Ctx->Taints.find(sID);
	if (it != Ctx->Taints.end())
		return it->second;
	return false;
}

bool TaintPass::markTaint(const std::string &sID, bool isSource = false)
{
	if (sID == "")
		return false;
	return Ctx->Taints.insert(std::make_pair(sID, isSource)).second;
}

// find and mark taint source
bool TaintPass::checkTaintSource(Instruction *I)
{
	Module *M = I->getParent()->getParent()->getParent();
	bool changed = false;

	if (MDNode *MD = I->getMetadata(MD_TaintSrc)) {
		VTS.insert(I);
		changed |= markTaint(getValueId(I), true);
		// mark all struct members as taint
		if (PointerType *PTy = dyn_cast<PointerType>(I->getType())) {
			if (StructType *STy = dyn_cast<StructType>(PTy->getElementType())) {
				for (unsigned i = 0; i < STy->getNumElements(); ++i)
					changed |= markTaint(getStructId(STy, M, i), true);
			}
		}
		(void )MD;
	}
	return changed;
}

// Propagate taint within a function
bool TaintPass::runOnFunction(Function *F)
{
	bool changed = false;
	
	for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
		bool tainted = false;
		Instruction *I = &*i;
		
		// Looking for taint sources
		changed |= checkTaintSource(I);
		
		// check if any operand is tainted
		for (unsigned j = 0; j < I->getNumOperands() && !tainted; ++j)
			tainted |= isTaint(I->getOperand(j));

		if (!tainted)
			continue;

		// update VTS and global taint
		VTS.insert(I);
		if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
			if (MDNode *ID = SI->getMetadata(MD_ID)) {
				StringRef sID = dyn_cast<MDString>
					(ID->getOperand(0))->getString();
				changed |= markTaint(sID);
			}
			if (GlobalVariable *GV = 
				dyn_cast<GlobalVariable>(SI->getPointerOperand())) {
				changed |= markTaint(getVarId(GV));
			}
		} else if (isa<ReturnInst>(I)) {
			changed |= markTaint(getRetId(F));
		} else if (CallInst *CI = dyn_cast<CallInst>(I)) {
			if (!CI->isInlineAsm() && Ctx->Callees.count(CI)) {
				FuncSet &CEEs = Ctx->Callees[CI];
				for (FuncSet::iterator j = CEEs.begin(), je = CEEs.end();
					 j != je; ++j) {
					
					// skip vaarg and builtin functions
					if ((*j)->isVarArg() 
						|| (*j)->getName().find('.') != StringRef::npos)
						continue;
					
					for (unsigned a = 0; a < CI->getNumArgOperands(); ++a) {
						if (isTaint(CI->getArgOperand(a))) {
							// mark this arg tainted on all possible callees
							changed |= markTaint(getArgId(*j, a));
						}
					}
				}
				if (isTaint(CI))
					changed |= markTaint(getRetId(CI));
			}
		}
	}
	return changed;
}

// write back
bool TaintPass::doFinalization(Module *M) {
	LLVMContext &VMCtx = M->getContext();
	MDNode *MD = MDNode::get(VMCtx, MDString::get(VMCtx, ""));
	for (Module::iterator f = M->begin(), fe = M->end(); f != fe; ++f) {
		Function *F = &*f;
		for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
			Instruction *I = &*i;
			if (isTaint(I)) {
				if (!I->getMetadata(MD_Taint))
					I->setMetadata(MD_Taint, MD);
			} else
				I->setMetadata(MD_Taint, NULL);
		}
	}
	return true;
}

bool TaintPass::doModulePass(Module *M) {
	bool changed = true, ret = false;

	while (changed) {
		changed = false;
		for (Module::iterator i = M->begin(), e = M->end(); i != e; ++i)
			changed |= runOnFunction(&*i);
		ret |= changed;
	}
	return ret;
}

// debug
void TaintPass::dumpTaints() {
	raw_ostream &OS = dbgs();
	for (TaintSet::iterator i = Ctx->Taints.begin(), 
		 e = Ctx->Taints.end(); i != e; ++i) {
		OS << (i->second ? "S " : "  ") << i->first << "\n";
	}
}
