#include "ValueGen.h"
#include <llvm/Constants.h>
#include <llvm/IntrinsicInst.h>
#include <llvm/Operator.h>
#include <llvm/ADT/APInt.h>
#include <llvm/Assembly/Writer.h>
#include <llvm/Support/GetElementPtrTypeIterator.h>
#include <llvm/Support/InstVisitor.h>
#include <llvm/Support/raw_ostream.h>
#include <assert.h>

using namespace llvm;

static void addRangeConstraints(SMTSolver &, SMTExpr, MDNode *);

namespace {

#define SMT    VG.SMT
#define TD     VG.TD

struct ValueVisitor : InstVisitor<ValueVisitor, SMTExpr> {
	ValueVisitor(ValueGen &VG)
		: VG(VG) {}

	SMTExpr analyze(Value *V) {
		if (!ValueGen::isAnalyzable(V)) {
			V->dump();
			assert(0 && "Unknown type!");
		}
		if (Instruction *I = dyn_cast<Instruction>(V))
			return visit(I);
		else if (Constant *C = dyn_cast<Constant>(V))
			return visitConstant(C);
		return mk_fresh(V);
	}

	SMTExpr visitInstruction(Instruction &I) {
		SMTExpr E = mk_fresh(&I);
		// Ranges are constants, so don't worry about recursion.
		if (MDNode *MD = I.getMetadata("intrange"))
			addRangeConstraints(SMT, E, MD);
		return E;
	}

	SMTExpr visitConstant(Constant *C) {
		if (ConstantInt *CI = dyn_cast<ConstantInt>(C))
			return SMT.bvconst(CI->getValue());
		if (isa<ConstantPointerNull>(C))
			return SMT.bvconst(APInt::getNullValue(getBitWidth(C)));
		if (GEPOperator *GEP = dyn_cast<GEPOperator>(C))
			return visitGEPOperator(*GEP);
		return mk_fresh(C);
	}

	SMTExpr visitTruncInst(TruncInst &I) {
		unsigned DstWidth = getBitWidth(I.getDestTy());
		return SMT.extract(DstWidth - 1, 0, get(I.getOperand(0)));
	}

	SMTExpr visitZExtInst(ZExtInst &I) {
		unsigned DstWidth = getBitWidth(I.getDestTy());
		unsigned SrcWidth = getBitWidth(I.getSrcTy());
		return SMT.zero_extend(DstWidth - SrcWidth, get(I.getOperand(0)));
	}

	SMTExpr visitSExtInst(SExtInst &I) {
		unsigned DstWidth = getBitWidth(I.getDestTy());
		unsigned SrcWidth = getBitWidth(I.getSrcTy());
		return SMT.sign_extend(DstWidth - SrcWidth, get(I.getOperand(0)));
	}

	SMTExpr visitBinaryOperator(BinaryOperator &I) {
		SMTExpr L = get(I.getOperand(0)), R = get(I.getOperand(1));
		switch (I.getOpcode()) {
		default: assert(0);
		case Instruction::Add:  return SMT.bvadd(L, R);
		case Instruction::Sub:  return SMT.bvsub(L, R);
		case Instruction::Mul:  return SMT.bvmul(L, R);
		case Instruction::UDiv: return SMT.bvudiv(L, R);
		case Instruction::SDiv: return SMT.bvsdiv(L, R);
		case Instruction::URem: return SMT.bvurem(L, R);
		case Instruction::SRem: return SMT.bvsrem(L, R);
		case Instruction::Shl:  return SMT.bvshl(L, R);
		case Instruction::LShr: return SMT.bvlshr(L, R);
		case Instruction::AShr: return SMT.bvashr(L, R);
		case Instruction::And:  return SMT.bvand(L, R);
		case Instruction::Or:   return SMT.bvor(L, R);
		case Instruction::Xor:  return SMT.bvxor(L, R);
		}
	}

	SMTExpr visitICmpInst(ICmpInst &I) {
		SMTExpr L = get(I.getOperand(0)), R = get(I.getOperand(1));
		switch (I.getPredicate()) {
		default: assert(0);
		case CmpInst::ICMP_EQ:  return SMT.eq(L, R); break;
		case CmpInst::ICMP_NE:  return SMT.ne(L, R); break;
		case CmpInst::ICMP_SGE: return SMT.bvsge(L, R); break;
		case CmpInst::ICMP_SGT: return SMT.bvsgt(L, R); break;
		case CmpInst::ICMP_SLE: return SMT.bvsle(L, R); break;
		case CmpInst::ICMP_SLT: return SMT.bvslt(L, R); break;
		case CmpInst::ICMP_UGE: return SMT.bvuge(L, R); break;
		case CmpInst::ICMP_UGT: return SMT.bvugt(L, R); break;
		case CmpInst::ICMP_ULE: return SMT.bvule(L, R); break;
		case CmpInst::ICMP_ULT: return SMT.bvult(L, R); break;
		}
	}

	SMTExpr visitSelectInst(SelectInst &I) {
		return SMT.ite(
			get(I.getCondition()),
			get(I.getTrueValue()),
			get(I.getFalseValue())
		);
	}

	SMTExpr visitExtractValueInst(ExtractValueInst &I) {
		IntrinsicInst *II = dyn_cast<IntrinsicInst>(I.getAggregateOperand());
		if (!II || II->getCalledFunction()->getName().find(".with.overflow.")
				== StringRef::npos)
			return mk_fresh(&I);
		SMTExpr L = get(II->getArgOperand(0));
		SMTExpr R = get(II->getArgOperand(1));
		assert(I.getNumIndices() == 1);
		switch (I.getIndices()[0]) {
		default: II->dump(); assert(0 && "Unknown overflow!");
		case 0:
			switch (II->getIntrinsicID()) {
			default: II->dump(); assert(0 && "Unknown overflow!");
			case Intrinsic::sadd_with_overflow:
			case Intrinsic::uadd_with_overflow:
				return SMT.bvadd(L, R);
			case Intrinsic::ssub_with_overflow:
			case Intrinsic::usub_with_overflow:
				return SMT.bvsub(L, R);
			case Intrinsic::smul_with_overflow:
			case Intrinsic::umul_with_overflow:
				return SMT.bvmul(L, R);
			}
		case 1:
			switch (II->getIntrinsicID()) {
			default: II->dump(); assert(0 && "Unknown overflow!");
			case Intrinsic::sadd_with_overflow:
				return SMT.bvsadd_overflow(L, R);
			case Intrinsic::uadd_with_overflow:
				return SMT.bvuadd_overflow(L, R);
			case Intrinsic::ssub_with_overflow:
				return SMT.bvssub_overflow(L, R);
			case Intrinsic::usub_with_overflow:
				return SMT.bvusub_overflow(L, R);
			case Intrinsic::smul_with_overflow:
				return SMT.bvsmul_overflow(L, R);
			case Intrinsic::umul_with_overflow:
				return SMT.bvumul_overflow(L, R);
			}
		}
		assert(I.getIndices()[0] == 1 && "FIXME!");

	}

	SMTExpr visitGetElementPtrInst(GetElementPtrInst &I) {
		return visitGEPOperator(cast<GEPOperator>(I));
	}

	SMTExpr visitGEPOperator(GEPOperator &GEP) {
		unsigned PtrSize = TD.getPointerSizeInBits(0);
		// Start from base.
		SMTExpr Offset = get(GEP.getPointerOperand());
		// Increase refcnt.
		SMT.incref(Offset);
		APInt ConstOffset = APInt::getNullValue(PtrSize);

		gep_type_iterator GTI = gep_type_begin(GEP);
		for (GEPOperator::op_iterator i = GEP.idx_begin(),
			 e = GEP.idx_end(); i != e; ++i, ++GTI) {
			Value *V = *i;
			// Skip zero index.
			ConstantInt *C = dyn_cast<ConstantInt>(V);
			if (C && C->isZero())
				continue;
			// For a struct, add the member offset.
			if (StructType *ST = dyn_cast<StructType>(*GTI)) {
				assert(C);
				unsigned FieldNo = C->getZExtValue();
				ConstOffset = ConstOffset + TD.getStructLayout(ST)->getElementOffset(FieldNo);
				continue;
			}
			// For an array, add the scaled element offset.
			uint64_t ElemSize = TD.getTypeAllocSize(*GTI);
			if (C) {
				ConstOffset = ConstOffset + C->getZExtValue() * ElemSize;
				continue;
			}
			SMTExpr SIdx = get(V);
			SMTExpr SElemSize = SMT.bvconst(APInt(PtrSize, ElemSize));
			SMTExpr LocalOffset = SMT.bvmul(SIdx, SElemSize);
			SMTExpr Tmp = SMT.bvadd(Offset, LocalOffset);
			// Don't delete SIdx;
			SMT.decref(SElemSize);
			SMT.decref(Offset);
			SMT.decref(LocalOffset);
			Offset = Tmp;
		}

		if (!ConstOffset)
			return Offset;

		// Merge constant offset.
		SMTExpr SConstOffset = SMT.bvconst(ConstOffset);
		SMTExpr Tmp = SMT.bvadd(Offset, SConstOffset);
		SMT.decref(Offset);
		SMT.decref(SConstOffset);
		return Tmp;
	}


	SMTExpr visitPtrToIntInst(PtrToIntInst &I) {
		Value *V = I.getOperand(0);
		SMTExpr E = get(V);
		unsigned PtrSize = getBitWidth(V);
		unsigned IntSize = getBitWidth(&I);
		if (IntSize > PtrSize)
			return SMT.zero_extend(IntSize - PtrSize, E);
		if (IntSize < PtrSize)
			return SMT.extract(IntSize - 1, 0, E);
		// IntSize == PtrSize.
		SMT.incref(E);
		return E;
	}

private:
	ValueGen &VG;

	SMTExpr get(Value *V) {
		return VG.get(V);
	}

	unsigned getBitWidth(Type *T) const {
		return TD.getTypeSizeInBits(T);
	}

	unsigned getBitWidth(Value *V) const {
		return getBitWidth(V->getType());
	}

	SMTExpr mk_fresh(Value *V) {
		std::string Name;
		{
			raw_string_ostream OS(Name);
			WriteAsOperand(OS, V, false);
			// Make name unique, e.g., undef.
			OS << "@" << V;
		}
		return SMT.bvvar(getBitWidth(V), Name.c_str());
	}

};

#undef SMT
#undef TD

} // anonymous namespace

ValueGen::ValueGen(DataLayout &TD, SMTSolver &SMT)
	: TD(TD), SMT(SMT) {}

ValueGen::~ValueGen() {
	for (iterator i = Cache.begin(), e = Cache.end(); i != e; ++i)
		SMT.decref(i->second);
}

bool ValueGen::isAnalyzable(llvm::Value *V) {
	return isAnalyzable(V->getType());
}

bool ValueGen::isAnalyzable(llvm::Type *T) {
	return T->isIntegerTy()
		|| T->isPointerTy()
		|| T->isFunctionTy();
}

SMTExpr ValueGen::get(Value *V) {
	// Don't use something like
	//   SMTExpr &E = ValueCache[S]
	// to update (S, E).  During visit the location may become invalid.
	SMTExpr E = Cache.lookup(V);
	if (!E) {
		E = ValueVisitor(*this).analyze(V);
		Cache[V] = E;
	}
	assert(E);
	return E;
}

void addRangeConstraints(SMTSolver &SMT, SMTExpr E, MDNode *MD) {
	// !range comes in pairs.
	unsigned n = MD->getNumOperands();
	assert(n % 2 == 0);
	for (unsigned i = 0; i != n; i += 2) {
		const APInt &Lo = cast<ConstantInt>(MD->getOperand(i))->getValue();
		const APInt &Hi = cast<ConstantInt>(MD->getOperand(i + 1))->getValue();
		// Ignore empty or full set.
		if (Lo == Hi)
			continue;
		SMTExpr Cmp0 = NULL, Cmp1 = NULL, Cond;
		// Ignore >= 0.
		if (!!Lo) {
			SMTExpr Tmp = SMT.bvconst(Lo);
			Cmp0 = SMT.bvuge(E, Tmp);
			SMT.decref(Tmp);
		}
		// Note that (< Hi) is not always correct.  Need to
		// ignore Hi == 0 (i.e., <= UMAX) or use (<= Hi - 1).
		if (!!Hi) {
			SMTExpr Tmp = SMT.bvconst(Hi);
			Cmp1 = SMT.bvult(E, Tmp);
			SMT.decref(Tmp);
		}
		if (!Cmp0) {
			Cond = Cmp1;
		} else if (!Cmp1) {
			Cond = Cmp0;
		} else {
			if (Lo.ule(Hi))	// [Lo, Hi).
				Cond = SMT.bvand(Cmp0, Cmp1);
			else		// Wrap: [Lo, UMAX] union [0, Hi).
				Cond = SMT.bvor(Cmp0, Cmp1);
			SMT.decref(Cmp0);
			SMT.decref(Cmp1);
		}
		SMT.assume(Cond);
		SMT.decref(Cond);
	}
}
