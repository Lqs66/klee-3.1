//===-- CVC5Builder.cpp ------------------------------------------*- C++ -*-====//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/config.h"

#ifdef ENABLE_CVC5

#include "CVC5Builder.h"
#include "klee/ADT/Bits.h"
#include "klee/Expr/Expr.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Support/ErrorHandling.h"
#include "llvm/ADT/StringExtras.h"

using namespace klee;

CVC5ArrayExprHash::CVC5ArrayExprHash() {}
CVC5ArrayExprHash::~CVC5ArrayExprHash() {}

void CVC5ArrayExprHash::clear() {
  _update_node_hash.clear();
  _array_hash.clear();
}

void CVC5ArrayExprHash::clearUpdates() {
  _update_node_hash.clear();
}

CVC5Builder::CVC5Builder(cvc5::TermManager& termManager, bool autoClear)
    : tm(termManager), autoClearConstructCache(autoClear) {}


CVC5Builder::~CVC5Builder() {
    clearConstructCache();
    _arr_hash.clear();
    constant_array_assertions.clear();
    fpToBvAssertions.clear();
}

// Create SMT-LIB bool constant true
// Z3 API Z3_mk_true <--> CVC5 API mkTrue
cvc5::Term CVC5Builder::getTrue() { return tm.mkTrue(); }

// Create SMT-LIB bool constant false
// Z3 API Z3_mk_false <--> CVC5 API mkFalse
cvc5::Term CVC5Builder::getFalse() { return tm.mkFalse(); }

// Create a bit vector with the least significant bit as 1 and all others as 0, according to width
cvc5::Term CVC5Builder::bvOne(unsigned width) { return tm.mkBitVector(width, 1); }

// Create a bit vector with all bits 0 according to width
cvc5::Term CVC5Builder::bvZero(unsigned width) { return tm.mkBitVector(width, 0); }

// Create bv constant -1, i.e., all bits are 1
cvc5::Term CVC5Builder::bvMinusOne(unsigned width) { return tm.mkTerm(cvc5::Kind::BITVECTOR_NOT, {tm.mkBitVector(width, 0)}); }

// Create a bit vector constant of specified width from a 32-bit unsigned integer
cvc5::Term CVC5Builder::bvConst32(unsigned width, uint32_t value) { return tm.mkBitVector(width, value); }
// Create a bit vector constant of specified width from a 64-bit unsigned integer
cvc5::Term CVC5Builder::bvConst64(unsigned width, uint64_t value) { return tm.mkBitVector(width, value); }

// Extract one bit from bv as a bool
cvc5::Term CVC5Builder::bvBoolExtract(const cvc5::Term& expr, int bit) {
    return eqExpr(bvExtract(expr, bit, bit), bvOne(1));
}

// Extract bits [top, bottom] from bit vector bv as a new bit vector
cvc5::Term CVC5Builder::bvExtract(const cvc5::Term& bv, unsigned top, unsigned bottom) {
    return tm.mkTerm(tm.mkOp(cvc5::Kind::BITVECTOR_EXTRACT, {top, bottom}), {castFPToBitVector(bv)});
}

// Create SMT-LIB term: equal(a, b)
// a equals b
cvc5::Term CVC5Builder::eqExpr(const cvc5::Term& a, const cvc5::Term& b) {
    // Handle implicit bitvector/float coercion
    cvc5::Sort aSort = a.getSort();
    cvc5::Sort bSort = b.getSort();

    cvc5::Term termA = a;
    cvc5::Term termB = b;

    if (aSort.isBitVector() && bSort.isFloatingPoint()) {
    // Coerce `a` to be a fp
    termA = castBvToFloat(termA);
    }

    if (aSort.isFloatingPoint() && bSort.isBitVector()) {
    // Coerce `b` to be a fp
    termB = castBvToFloat(termB);
    }

    return tm.mkTerm(cvc5::Kind::EQUAL, {termA, termB});
}

// Create SMT-LIB term: not(a)
// a negated
cvc5::Term CVC5Builder::notExpr(const cvc5::Term& expr) {
    return tm.mkTerm(cvc5::Kind::NOT, {expr});
}

// Create SMT-LIB term: and(a, b)
// a and b
cvc5::Term CVC5Builder::andExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::AND, {lhs, rhs});
}

// Create SMT-LIB term: or(a, b)
// a or b
cvc5::Term CVC5Builder::orExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::OR, {lhs, rhs});
}

// Check if two bool values are equal
cvc5::Term CVC5Builder::iffExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    cvc5::Sort lhsSort = lhs.getSort();
    cvc5::Sort rhsSort = rhs.getSort();
    assert(lhsSort == rhsSort && "lhs and rhs sorts must match");
    assert(lhsSort.isBoolean() && "args must have BOOL sort");
    return tm.mkTerm(cvc5::Kind::EQUAL, {lhs, rhs});
}

// Create SMT-LIB term: bvnot(a)
// a bitwise negated
cvc5::Term CVC5Builder::bvNotExpr(const cvc5::Term& expr) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_NOT, {castFPToBitVector(expr)});
}

// Create SMT-LIB term: bvand(a, b)
// a bitwise and b
cvc5::Term CVC5Builder::bvAndExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_AND, {castFPToBitVector(lhs), castFPToBitVector(rhs)});
}

// Create SMT-LIB term: bvor(a, b)
// a bitwise or b
cvc5::Term CVC5Builder::bvOrExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_OR, {castFPToBitVector(lhs), castFPToBitVector(rhs)});
}

// Create SMT-LIB term: bvxor(a, b)
// a bitwise xor b
cvc5::Term CVC5Builder::bvXorExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_XOR, {castFPToBitVector(lhs), castFPToBitVector(rhs)});
}

// Perform sign extension on bit vector
cvc5::Term CVC5Builder::bvSignExtend(const cvc5::Term& src, unsigned width) {
    cvc5::Term srcAsBv = castFPToBitVector(src);
    unsigned srcWidth = srcAsBv.getSort().getBitVectorSize();
    assert(srcWidth <= width && "attempted to extend longer data");
    return tm.mkTerm(tm.mkOp(cvc5::Kind::BITVECTOR_SIGN_EXTEND, {width - srcWidth}), {srcAsBv});
}

// Create SMT-LIB term: store(Array, Index, Value)
// Write Value to Array at position Index
cvc5::Term CVC5Builder::writeExpr(const cvc5::Term& array, const cvc5::Term& index, const cvc5::Term& value) {
    return tm.mkTerm(cvc5::Kind::STORE, {array, index, value});
}

// Create SMT-LIB term: select(Array, Index)
// Read element at Index from Array
cvc5::Term CVC5Builder::readExpr(const cvc5::Term& array, const cvc5::Term& index) {
    return tm.mkTerm(cvc5::Kind::SELECT, {array, index});
}

// Create SMT-LIB term: ite(Condition, WhenTrue, WhenFalse)
// Select WhenTrue or WhenFalse according to Condition
// Unlike Z3Builder, we choose to cast bitvector to FP instead of FP to bitvector
cvc5::Term CVC5Builder::iteExpr(const cvc5::Term& condition, const cvc5::Term& whenTrue, const cvc5::Term& whenFalse) {
    // Handle implicit bitvector/float coercion
    cvc5::Sort whenTrueSort = whenTrue.getSort();
    cvc5::Sort whenFalseSort = whenFalse.getSort();

    cvc5::Term termTrue = whenTrue;
    cvc5::Term termFalse = whenFalse;

    if (whenTrueSort.isBitVector() && whenFalseSort.isFloatingPoint()) {
        // Coerce `whenTrue` to be a float
        termTrue = castBvToFloat(termTrue);
    }

    if (whenTrueSort.isFloatingPoint() && whenFalseSort.isBitVector()) {
        // Coerce `whenFalse` to be a float
        termFalse = castBvToFloat(termFalse);
    }

    return tm.mkTerm(cvc5::Kind::ITE, {condition, termTrue, termFalse});
}

// Bit-vector unsigned less than.
cvc5::Term CVC5Builder::bvLtExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_ULT, {castFPToBitVector(lhs), castFPToBitVector(rhs)});
}

// Bit-vector unsigned less than or equal.
cvc5::Term CVC5Builder::bvLeExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_ULE, {castFPToBitVector(lhs), castFPToBitVector(rhs)});
}

// signed bit-vector less than.
cvc5::Term CVC5Builder::sbvLtExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_SLT, {castFPToBitVector(lhs), castFPToBitVector(rhs)});
}

// signed bit-vector less than or equal.
cvc5::Term CVC5Builder::sbvLeExpr(const cvc5::Term& lhs, const cvc5::Term& rhs) {
    return tm.mkTerm(cvc5::Kind::BITVECTOR_SLE, {castFPToBitVector(lhs), castFPToBitVector(rhs)});
}

// Logical left shift operation for integers
cvc5::Term CVC5Builder::bvLeftShift(const cvc5::Term& expr, unsigned shift) {
  cvc5::Term exprAsBv = castFPToBitVector(expr);
  unsigned width = exprAsBv.getSort().getBitVectorSize();
  if (shift == 0) return expr;
  if (shift >= width) return bvZero(width); // Overshift to zero
  return tm.mkTerm(cvc5::Kind::BITVECTOR_SHL, {exprAsBv, bvConst32(width, shift)});
}

// Logical right shift operation for integers
cvc5::Term CVC5Builder::bvRightShift(const cvc5::Term& expr, unsigned shift) {
  cvc5::Term exprAsBv = castFPToBitVector(expr);
  unsigned width = exprAsBv.getSort().getBitVectorSize();
  if (shift == 0) return expr;
  if (shift >= width) return bvZero(width); // Overshift to zero
  return tm.mkTerm(cvc5::Kind::BITVECTOR_LSHR, {exprAsBv, bvConst32(width, shift)});
}

// left shift by a variable amount on an expression of the specified width
cvc5::Term CVC5Builder::bvVarLeftShift(const cvc5::Term& expr, const cvc5::Term& shift) {
  cvc5::Term exprAsBv = castFPToBitVector(expr);
  cvc5::Term shiftAsBv = castFPToBitVector(shift);
  unsigned width = exprAsBv.getSort().getBitVectorSize();
  cvc5::Term res = bvZero(width);

  // construct a big if-then-elif-elif-... with one case per possible shift
  // amount
  for (int i = width - 1; i >= 0; i--) {
    res = iteExpr(eqExpr(shiftAsBv, bvConst32(width, i)),
                  bvLeftShift(exprAsBv, i), res);
  }

  // If overshifting, shift to zero
  cvc5::Term ex = bvLtExpr(shiftAsBv, bvConst32(shiftAsBv.getSort().getBitVectorSize(), width));
  res = iteExpr(ex, res, bvZero(width));
  return res;
}

cvc5::Term CVC5Builder::bvVarRightShift(const cvc5::Term& expr, const cvc5::Term& shift) {
  cvc5::Term exprAsBv = castFPToBitVector(expr);
  cvc5::Term shiftAsBv = castFPToBitVector(shift);
  unsigned width = exprAsBv.getSort().getBitVectorSize();
  cvc5::Term res = bvZero(width);

  // construct a big if-then-elif-elif-... with one case per possible shift
  // amount
  for (int i = width - 1; i >= 0; i--) {
    res = iteExpr(eqExpr(shiftAsBv, bvConst32(width, i)),
                  bvRightShift(exprAsBv, i), res);
  }

  // If overshifting, shift to zero
  cvc5::Term ex = bvLtExpr(shiftAsBv, bvConst32(shiftAsBv.getSort().getBitVectorSize(), width));
  res = iteExpr(ex, res, bvZero(width));
  return res;
}

cvc5::Term CVC5Builder::bvVarArithRightShift(const cvc5::Term& expr, const cvc5::Term& shift) {
  cvc5::Term exprAsBv = castFPToBitVector(expr);
  cvc5::Term shiftAsBv = castFPToBitVector(shift);
  unsigned width = exprAsBv.getSort().getBitVectorSize();

  // get the sign bit to fill with
  cvc5::Term signedBool = bvBoolExtract(exprAsBv, width - 1);

  // start with the result if shifting by width-1
  cvc5::Term res = constructAShrByConstant(exprAsBv, width - 1, signedBool);

  // construct a big if-then-elif-elif-... with one case per possible shift
  // amount
  for (int i = width - 2; i >= 0; i--) {
    res = iteExpr(eqExpr(shiftAsBv, bvConst32(width, i)),
                  constructAShrByConstant(exprAsBv, i, signedBool), res);
  }

  // If overshifting, shift to zero
  cvc5::Term ex = bvLtExpr(shiftAsBv, bvConst32(shiftAsBv.getSort().getBitVectorSize(), width));
  res = iteExpr(ex, res, bvZero(width));
  return res;
}

cvc5::Term CVC5Builder::constructAShrByConstant(const cvc5::Term& expr, unsigned shift, const cvc5::Term& isSigned) {
    cvc5::Term exprAsBv = castFPToBitVector(expr);
    unsigned width = exprAsBv.getSort().getBitVectorSize();

    if (shift == 0) {
        return exprAsBv;
    } else if (shift >= width) {
        return bvZero(width); // Overshift to zero
    } else {
        // FIXME: Is this really the best way to interact with CVC5?
        return iteExpr(
            isSigned,
            tm.mkTerm(cvc5::Kind::BITVECTOR_CONCAT, {bvMinusOne(shift),
                      bvExtract(exprAsBv, width - 1, shift)}),
            bvRightShift(exprAsBv, shift));
    }
}

cvc5::Sort CVC5Builder::getBvSort(unsigned width) {
    return tm.mkBitVectorSort(width);
}

cvc5::Sort CVC5Builder::getArraySort(cvc5::Sort domainSort, cvc5::Sort rangeSort) {
    return tm.mkArraySort(domainSort, rangeSort);
}

std::vector<uint32_t> CVC5Builder::getFPExpAndSignFromBitWidth(unsigned bitWidth) {
   switch(bitWidth) {
        case Expr::Int16: return{5, 11};
        case Expr::Int32: return {8, 24};
        case Expr::Int64: return {11, 53};
        case Expr::Fl80: return {15, 64};
        case Expr::Int128: return {15, 113};
        default: assert(0 && "bitWidth cannot be converted to a float sort");
    } 
}

// Create floating point Sort according to bit width
cvc5::Sort CVC5Builder::getFloatSortFromBitWidth(unsigned bitWidth) {
    switch(bitWidth) {
        case Expr::Int16: return tm.mkFloatingPointSort(5, 11);
        case Expr::Int32: return tm.mkFloatingPointSort(8, 24);
        case Expr::Int64: return tm.mkFloatingPointSort(11, 53);
        case Expr::Fl80: return tm.mkFloatingPointSort(15, 64);
        case Expr::Int128: return tm.mkFloatingPointSort(15, 113);
        default: assert(0 && "bitWidth cannot be converted to a float sort");
    }
}

cvc5::Term CVC5Builder::getRoundingModeSort(llvm::APFloat::roundingMode rm) {
    switch(rm) {
        case llvm::APFloat::rmNearestTiesToEven: return tm.mkRoundingMode(cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
        case llvm::APFloat::rmTowardPositive: return tm.mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_POSITIVE);
        case llvm::APFloat::rmTowardNegative: return tm.mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE);
        case llvm::APFloat::rmTowardZero: return tm.mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_ZERO);
        case llvm::APFloat::rmNearestTiesToAway: return tm.mkRoundingMode(cvc5::RoundingMode::ROUND_NEAREST_TIES_TO_AWAY);
        default: assert(0 && "unhandled rounding mode");
    }
}

// Convert bit vector e to floating point
// Supports 16, 32, 64, 128 bit floating point
// Unlike Z3 Builder, we do not support Fl80
cvc5::Term CVC5Builder::castBvToFloat(const cvc5::Term& e) {
    cvc5::Sort currentSort = e.getSort();
    if (currentSort.isFloatingPoint()) {
        // Already a float
        return e;
    }
    if (currentSort.isBitVector()) {
        unsigned bitWidth = currentSort.getBitVectorSize();
        switch (bitWidth) {
        case Expr::Int16: {
            cvc5::Op bvToFpOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {5, 11});
            return tm.mkTerm(bvToFpOp, {e});
        }
        case Expr::Int32: {
            cvc5::Op bvToFpOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {8, 24});
            return tm.mkTerm(bvToFpOp, {e});
        }
        case Expr::Int64: {
            cvc5::Op bvToFpOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {11, 53});
            return tm.mkTerm(bvToFpOp, {e});
        }
        case Expr::Int128: {
            cvc5::Op bvToFpOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {15, 113});
            return tm.mkTerm(bvToFpOp, {e});
        }
        default:
            assert(0 && "Unhandled width when casting bitvector to float");
        }
    }
    assert(0 && "castBvToFloat: unsupported sort");
}

// cvc5::Term CVC5Builder::castFPToBitVector(const cvc5::Term& e) {
//     cvc5::Sort currentSort = e.getSort();
//     if (currentSort.isBitVector()) {
//         // Already a bitvector
//         return e;
//     }
//     if (currentSort.isFloatingPoint()) {
//         unsigned exponentBits = currentSort.getFloatingPointExponentSize();
//         unsigned significandBits = currentSort.getFloatingPointSignificandSize(); // Includes implicit bit
//         unsigned floatWidth = exponentBits + significandBits;
        
//         switch (floatWidth) {
//         case Expr::Int16:
//         case Expr::Int32:
//         case Expr::Int64:
//         case Expr::Int128:
//             // Standard IEEE formats - use direct conversion
//             return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_TO_IEEE_BV, {e});
//         default:
//             assert(0 && "Unhandled width when casting float to bitvector");
//         }
//     }
//     assert(0 && "castFPToBitVector: unsupported sort");
// }

/*
Note:
    There is no function for converting from (_ FloatingPoint eb sb) to the
    corresponding IEEE 754-2008 binary format, as a bit vector (_ BitVec m) with 
    m = eb + sb, because (_ NaN eb sb) has multiple, well-defined representations.
    Instead, an encoding of the kind below is recommended, where f is a term
    of sort (_ FloatingPoint eb sb):

    (declare-fun b () (_ BitVec m))
    (assert (= ((_ to_fp eb sb) b) f))

    https://smt-lib.org/theories-FloatingPoint.shtml
*/
cvc5::Term CVC5Builder::castFPToBitVector(const cvc5::Term& e) {
    cvc5::Sort currentSort = e.getSort();
    if (currentSort.isBitVector()) {
        // Already a bitvector
        return e;
    }
    if (currentSort.isFloatingPoint()) {
        unsigned exponentBits = currentSort.getFloatingPointExponentSize();
        unsigned significandBits = currentSort.getFloatingPointSignificandSize();
        unsigned floatWidth = exponentBits + significandBits;
        cvc5::Sort bvSort = tm.mkBitVectorSort(floatWidth);
        cvc5::Term b = tm.mkConst(bvSort);
        cvc5::Op toFpOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {exponentBits, significandBits});
        cvc5::Term to_fp = tm.mkTerm(toFpOp, {b});
        cvc5::Term eq = tm.mkTerm(cvc5::Kind::EQUAL, {to_fp, e});
        fpToBvAssertions[b] = eq;
        return b;
    }
    assert(0 && "castFPToBitVector: unsupported sort");
    return cvc5::Term();
}

void CVC5Builder::FPCastWidthAssert(int *width_out, char const* msg) {
#if LLVM_VERSION_CODE >= LLVM_VERSION(4, 0)
  assert(&(ConstantExpr::widthToFloatSemantics(*width_out)) !=
    &(llvm::APFloat::Bogus()) && msg);
#else
  assert(&(ConstantExpr::widthToFloatSemantics(*width_out)) !=
    &(llvm::APFloat::Bogus) && msg);
#endif
}

/** if *width_out!=1 then result is a bitvector,
otherwise it is a bool */
cvc5::Term CVC5Builder::constructActual(ref<Expr> e, int *width_out) {
    int width;
    if (!width_out) width_out = &width;

    ++stats::queryConstructs;

    switch (e->getKind()) {
        case Expr::Constant: {
            ConstantExpr *CE = cast<ConstantExpr>(e);
            *width_out = CE->getWidth();
            if (*width_out == 1) return CE->isTrue() ? getTrue() : getFalse();
            if (CE->isFloat()) {
                std::vector<uint32_t> expAndSign = getFPExpAndSignFromBitWidth(*width_out);
                if (*width_out == 32) {
                    return tm.mkFloatingPoint(expAndSign[0], expAndSign[1], bvConst32(*width_out, CE->getZExtValue(32)));
                } else if (*width_out == 64) {
                    return tm.mkFloatingPoint(expAndSign[0], expAndSign[1], bvConst64(*width_out, CE->getZExtValue()));
                }
            }
            cvc5::Term Res;
            if (*width_out <= 32) {
                Res = bvConst32(*width_out, CE->getZExtValue(32));
            } else if (*width_out <= 64) {
                Res = bvConst64(*width_out, CE->getZExtValue());
            }else{
                ref<ConstantExpr> Tmp = CE;
                Res = bvConst64(64, Tmp->Extract(0, 64)->getZExtValue());
                while (Tmp->getWidth() > 64) {
                    Tmp = Tmp->Extract(64, Tmp->getWidth() - 64);
                    unsigned Width = std::min(64U, Tmp->getWidth());
                    Res = tm.mkTerm(cvc5::Kind::BITVECTOR_CONCAT, {bvConst64(Width, Tmp->Extract(0, Width)->getZExtValue()), Res});
                }   
            }
            // Coerce to float if necesary
            if (CE->isFloat()) {
                Res = castBvToFloat(Res);
            }

            return Res;
        }

        // Special
        case Expr::NotOptimized: {
            NotOptimizedExpr *noe = cast<NotOptimizedExpr>(e);
            return construct(noe->src, width_out);
        }

        // Convert to array
        case Expr::Read: {
            ReadExpr *re = cast<ReadExpr>(e);
            assert(re && re->updates.root);
            *width_out = re->updates.root->getRange();
            return readExpr(getArrayForUpdate(re->updates.root, re->updates.head.get()), construct(re->index, 0));
        }

        case Expr::Select: {
            SelectExpr *se = cast<SelectExpr>(e);
            return iteExpr(construct(se->cond, 0), construct(se->trueExpr, width_out), construct(se->falseExpr, width_out));
        }

        case Expr::Concat: {
            ConcatExpr *ce = cast<ConcatExpr>(e);
            unsigned numKids = ce->getNumKids();
            cvc5::Term res = construct(ce->getKid(numKids - 1), 0);
            for (int i = numKids - 2; i >= 0; i--) {
                res = tm.mkTerm(cvc5::Kind::BITVECTOR_CONCAT, {construct(ce->getKid(i), 0), res});
            }
            *width_out = ce->getWidth();
            return res;
        }

        case Expr::Extract: {
            ExtractExpr *ee = cast<ExtractExpr>(e);
            cvc5::Term src = construct(ee->expr, width_out);
            *width_out = ee->getWidth();
            if (*width_out == 1) {
                return bvBoolExtract(src, ee->offset);
            }
            return bvExtract(src, ee->offset + *width_out - 1, ee->offset);
        }

        // Casting
        case Expr::ZExt: {
            CastExpr *ce = cast<CastExpr>(e);
            int srcWidth;
            cvc5::Term src = construct(ce->src, &srcWidth);
            *width_out = ce->getWidth();
            if (srcWidth == 1) {
                return iteExpr(src, bvOne(*width_out), bvZero(*width_out));
            } else {
                assert(*width_out > srcWidth && "Invalid width_out");
                cvc5::Op zextOp = tm.mkOp(cvc5::Kind::BITVECTOR_ZERO_EXTEND, {*width_out - srcWidth});
                return tm.mkTerm(zextOp, {castFPToBitVector(src)});
            }
        }

        case Expr::SExt: {
            CastExpr *ce = cast<CastExpr>(e);
            int srcWidth;
            cvc5::Term src = construct(ce->src, &srcWidth);
            *width_out = ce->getWidth();
            if (srcWidth == 1) {
                return iteExpr(src, bvMinusOne(*width_out), bvZero(*width_out));
            } else {
                return bvSignExtend(src, *width_out);
            }
        }

        case Expr::FPExt: {
            int srcWidth;
            FPExtExpr *ce = cast<FPExtExpr>(e);
            cvc5::Term src = castBvToFloat(construct(ce->src, &srcWidth));
            *width_out = ce->getWidth();
            FPCastWidthAssert(width_out, "Invalid FPExt width");
            assert(*width_out >= srcWidth && "Invalid FPExt");

            cvc5::Op fpextOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_FP, getFPExpAndSignFromBitWidth(*width_out));
            return tm.mkTerm(
                fpextOp,
                {getRoundingModeSort(llvm::APFloat::rmNearestTiesToEven),
                src}
            );
        }

        case Expr::FPTrunc: {
            int srcWidth;
            FPTruncExpr *ce = cast<FPTruncExpr>(e);
            cvc5::Term src = castBvToFloat(construct(ce->src, &srcWidth));
            *width_out = ce->getWidth();
            FPCastWidthAssert(width_out, "Invalid FPTrunc width");
            assert(*width_out <= srcWidth && "Invalid FPTrunc");
            cvc5::Op fptruncOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_FP, getFPExpAndSignFromBitWidth(*width_out));
            return tm.mkTerm(
                fptruncOp,
                {getRoundingModeSort(ce->roundingMode),
                src}
            );
        }

        case Expr::FPToUI: {
            int srcWidth;
            FPToUIExpr *ce = cast<FPToUIExpr>(e);
            cvc5::Term src = castBvToFloat(construct(ce->src, &srcWidth));
            *width_out = ce->getWidth();
            FPCastWidthAssert(width_out, "Invalid FPToUI width");
            cvc5::Op fpToUIOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_UBV, {*width_out});
            return tm.mkTerm(
                fpToUIOp,
                {getRoundingModeSort(ce->roundingMode), src}
            );
        }

        case Expr::FPToSI: {
            int srcWidth;
            FPToSIExpr *ce = cast<FPToSIExpr>(e);
            cvc5::Term src = castBvToFloat(construct(ce->src, &srcWidth));
            *width_out = ce->getWidth();
            FPCastWidthAssert(width_out, "Invalid FPToSI width");
            cvc5::Op fpToSIOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_SBV, {*width_out});
            return tm.mkTerm(
                fpToSIOp,
                {getRoundingModeSort(ce->roundingMode), src}
            );
        }

        case Expr::UIToFP: {
            int srcWidth;
            UIToFPExpr *ce = cast<UIToFPExpr>(e);
            cvc5::Term src = castFPToBitVector(construct(ce->src, &srcWidth));
            *width_out = ce->getWidth();
            FPCastWidthAssert(width_out, "Invalid UIToFP width");
            cvc5::Op fpToUIOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_UBV, getFPExpAndSignFromBitWidth(*width_out));
            return tm.mkTerm(
                fpToUIOp,
                {getRoundingModeSort(ce->roundingMode),
                src}
            );
        }

        case Expr::SIToFP: {
            int srcWidth;
            SIToFPExpr *ce = cast<SIToFPExpr>(e);
            cvc5::Term src = castFPToBitVector(construct(ce->src, &srcWidth));
            *width_out = ce->getWidth();
            FPCastWidthAssert(width_out, "Invalid SIToFP width");
            cvc5::Op fpToSIOp = tm.mkOp(cvc5::Kind::FLOATINGPOINT_TO_FP_FROM_SBV, getFPExpAndSignFromBitWidth(*width_out));
            return tm.mkTerm(
                fpToSIOp,
                {getRoundingModeSort(ce->roundingMode),
                src}
            );
        }

        // Arithmetic
        case Expr::Add: {
            AddExpr *ae = cast<AddExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(ae->left, width_out));
            cvc5::Term right = castFPToBitVector(construct(ae->right, width_out));
            assert(*width_out != 1 && "uncanonicalized add");
            cvc5::Term res = tm.mkTerm(cvc5::Kind::BITVECTOR_ADD, {left, right});
            assert(res.getSort().getBitVectorSize() == static_cast<unsigned>(*width_out) &&
                   "width mismatch");
            return res;
        }

        case Expr::Sub: {
            SubExpr *se = cast<SubExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(se->left, width_out));
            cvc5::Term right = castFPToBitVector(construct(se->right, width_out));
            assert(*width_out != 1 && "uncanonicalized sub");
            cvc5::Term res = tm.mkTerm(cvc5::Kind::BITVECTOR_SUB, {left, right});
            assert(res.getSort().getBitVectorSize() == static_cast<unsigned>(*width_out) &&
                   "width mismatch");
            return res;
        }

        case Expr::Mul: {
            MulExpr *me = cast<MulExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(me->left, width_out));
            cvc5::Term right = castFPToBitVector(construct(me->right, width_out));
            assert(*width_out != 1 && "uncanonicalized mul");
            cvc5::Term res = tm.mkTerm(cvc5::Kind::BITVECTOR_MULT, {left, right});
            assert(res.getSort().getBitVectorSize() == static_cast<unsigned>(*width_out) &&
                   "width mismatch");
            return res;
        }

        case Expr::UDiv: {
            UDivExpr *de = cast<UDivExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(de->left, width_out));
            assert(*width_out != 1 && "uncanonicalized udiv");

            if (ConstantExpr *CE = dyn_cast<ConstantExpr>(de->right)) {
                if (CE->getWidth() <= 64) {
                    uint64_t divisor = CE->getZExtValue();
                    if (bits64::isPowerOfTwo(divisor))
                        return bvRightShift(left, bits64::indexOfSingleBit(divisor));
                }
            }
            cvc5::Term right = castFPToBitVector(construct(de->right, width_out));
            cvc5::Term res = tm.mkTerm(cvc5::Kind::BITVECTOR_UDIV, {left, right});
            assert(res.getSort().getBitVectorSize() == static_cast<unsigned>(*width_out) &&
                   "width mismatch");
            return res;
        }

        case Expr::SDiv: {
            SDivExpr *de = cast<SDivExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(de->left, width_out));
            cvc5::Term right = castFPToBitVector(construct(de->right, width_out));
            assert(*width_out != 1 && "uncanonicalized sdiv");
            cvc5::Term res = tm.mkTerm(cvc5::Kind::BITVECTOR_SDIV, {left, right});
            assert(res.getSort().getBitVectorSize() == static_cast<unsigned>(*width_out) &&
                   "width mismatch");
            return res;
        }

        case Expr::URem: {
            URemExpr *de = cast<URemExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(de->left, width_out));
            cvc5::Term right = castFPToBitVector(construct(de->right, width_out));
            assert(*width_out != 1 && "uncanonicalized urem");
            cvc5::Term res = tm.mkTerm(cvc5::Kind::BITVECTOR_UREM, {left, right});
            assert(res.getSort().getBitVectorSize() == static_cast<unsigned>(*width_out) && "width mismatch");
            return res;
        }

        case Expr::SRem: {
            SRemExpr *de = cast<SRemExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(de->left, width_out));
            cvc5::Term right = castFPToBitVector(construct(de->right, width_out));
            assert(*width_out != 1 && "uncanonicalized srem");
            cvc5::Term res = tm.mkTerm(cvc5::Kind::BITVECTOR_SREM, {left, right});
            assert(res.getSort().getBitVectorSize() == static_cast<unsigned>(*width_out) && "width mismatch");
            return res;
        }

        // Bitwise
        case Expr::Not: {
            NotExpr *ne = cast<NotExpr>(e);
            cvc5::Term expr = construct(ne->expr, width_out);
            if (*width_out == 1) return notExpr(expr);
            return bvNotExpr(expr);
        }

        case Expr::And: {
            AndExpr *ae = cast<AndExpr>(e);
            cvc5::Term left = construct(ae->left, width_out);
            cvc5::Term right = construct(ae->right, width_out);
            if (*width_out == 1) return andExpr(left, right);
            return bvAndExpr(left, right);
        }
        
        case Expr::Or: {
            OrExpr *oe = cast<OrExpr>(e);
            cvc5::Term left = construct(oe->left, width_out);
            cvc5::Term right = construct(oe->right, width_out);
            if (*width_out == 1) return orExpr(left, right);
            return bvOrExpr(left, right);
        }
        
        case Expr::Xor: {
            XorExpr *xe = cast<XorExpr>(e);
            cvc5::Term left = construct(xe->left, width_out);
            cvc5::Term right = construct(xe->right, width_out);
            if (*width_out == 1) {
                return iteExpr(left, notExpr(right), right);
            }
            return bvXorExpr(left, right);
        }

        case Expr::Shl: {
            ShlExpr *se = cast<ShlExpr>(e);
            cvc5::Term left = construct(se->left, width_out);
            assert(*width_out != 1 && "uncanonicalized shl");

            if (ConstantExpr *CE = dyn_cast<ConstantExpr>(se->right)) {
                return bvLeftShift(left, (unsigned)CE->getLimitedValue());
            } else {
                int shiftWidth;
                cvc5::Term amount = construct(se->right, &shiftWidth);
                return bvVarLeftShift(left, amount);
            }
        }

        case Expr::LShr: {
            LShrExpr *lse = cast<LShrExpr>(e);
            cvc5::Term left = construct(lse->left, width_out);
            assert(*width_out != 1 && "uncanonicalized lshr");

            if (ConstantExpr *CE = dyn_cast<ConstantExpr>(lse->right)) {
                return bvRightShift(left, (unsigned)CE->getLimitedValue());
            } else {
                int shiftWidth;
                cvc5::Term amount = construct(lse->right, &shiftWidth);
                return bvVarRightShift(left, amount);
            }
        }

        case Expr::AShr: {
            AShrExpr *ase = cast<AShrExpr>(e);
            cvc5::Term left = castFPToBitVector(construct(ase->left, width_out));
            assert(*width_out != 1 && "uncanonicalized ashr");

            if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ase->right)) {
                unsigned shift = (unsigned)CE->getLimitedValue();
                cvc5::Term signedBool = bvBoolExtract(left, *width_out - 1);
                return constructAShrByConstant(left, shift, signedBool);
            } else {
                int shiftWidth;
                cvc5::Term amount = construct(ase->right, &shiftWidth);
                return bvVarArithRightShift(left, amount);
            }
        }

        // Comparison
        case Expr::Eq: {
            EqExpr *ee = cast<EqExpr>(e);
            cvc5::Term left = construct(ee->left, width_out);
            cvc5::Term right = construct(ee->right, width_out);
            if (*width_out == 1) {
                if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ee->left)) {
                    if (CE->isTrue()) {
                        return right;
                    } 
                    return notExpr(right);
                } else {
                    return iffExpr(left, right);
                }
            } else {
                *width_out = 1;
                return eqExpr(left, right);
            }
        }

        case Expr::Ult: {
            UltExpr *ue = cast<UltExpr>(e);
            cvc5::Term left = construct(ue->left, width_out);
            cvc5::Term right = construct(ue->right, width_out);
            assert(*width_out != 1 && "uncanonicalized ult");
            *width_out = 1;
            return bvLtExpr(left, right);
        }

        case Expr::Ule: {
            UleExpr *ue = cast<UleExpr>(e);
            cvc5::Term left = construct(ue->left, width_out);
            cvc5::Term right = construct(ue->right, width_out);
            assert(*width_out != 1 && "uncanonicalized ule");
            *width_out = 1;
            return bvLeExpr(left, right);
        }

        case Expr::Slt: {
            SltExpr *se = cast<SltExpr>(e);
            cvc5::Term left = construct(se->left, width_out);
            cvc5::Term right = construct(se->right, width_out);
            assert(*width_out != 1 && "uncanonicalized slt");
            *width_out = 1;
            return sbvLtExpr(left, right);
        }

        case Expr::Sle: {
            SleExpr *se = cast<SleExpr>(e);
            cvc5::Term left = construct(se->left, width_out);
            cvc5::Term right = construct(se->right, width_out);
            assert(*width_out != 1 && "uncanonicalized sle");
            *width_out = 1;
            return sbvLeExpr(left, right);
        }

        case Expr::FOEq: {
            FOEqExpr *foe = cast<FOEqExpr>(e);
            cvc5::Term left = castBvToFloat(construct(foe->left, width_out));
            cvc5::Term right = castBvToFloat(construct(foe->right, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_EQ, {left, right});
        }

        case Expr::FOLt: {
            FOLtExpr *fol = cast<FOLtExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fol->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fol->right, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_LT, {left, right});
        }

        case Expr::FOLe: {
            FOLeExpr *fole = cast<FOLeExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fole->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fole->right, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_LEQ, {left, right});
        }

        case Expr::FOGt: {
            FOGtExpr *fog = cast<FOGtExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fog->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fog->right, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_GT, {left, right});
        }

        case Expr::FOGe: {
            FOGeExpr *foge = cast<FOGeExpr>(e);
            cvc5::Term left = castBvToFloat(construct(foge->left, width_out));
            cvc5::Term right = castBvToFloat(construct(foge->right, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_GEQ, {left, right});
        }

        case Expr::IsNaN: {
            IsNaNExpr *isnan = cast<IsNaNExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(isnan->expr, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_IS_NAN, {arg});
        }

        case Expr::IsInfinite: {
            IsInfiniteExpr *isinf = cast<IsInfiniteExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(isinf->expr, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_IS_INF, {arg});
        }

        case Expr::IsNormal: {
            IsNormalExpr *isnorm = cast<IsNormalExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(isnorm->expr, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_IS_NORMAL, {arg});
        }

        case Expr::IsSubnormal: {
            IsSubnormalExpr *issubnorm = cast<IsSubnormalExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(issubnorm->expr, width_out));
            *width_out = 1;
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_IS_SUBNORMAL, {arg});
        }

        case Expr::FAdd: {
            FAddExpr *fae = cast<FAddExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fae->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fae->right, width_out));
            assert(*width_out != 1 && "uncanonicalized FAdd");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_ADD, {getRoundingModeSort(fae->roundingMode), left, right});
        }

        case Expr::FSub: {
            FSubExpr *fse = cast<FSubExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fse->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fse->right, width_out));
            assert(*width_out != 1 && "uncanonicalized FSub");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_SUB, {getRoundingModeSort(fse->roundingMode), left, right});
        }

        case Expr::FMul: {
            FMulExpr *fme = cast<FMulExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fme->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fme->right, width_out));
            assert(*width_out != 1 && "uncanonicalized FMul");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_MULT, {getRoundingModeSort(fme->roundingMode), left, right});
        }

        case Expr::FDiv: {
            FDivExpr *fde = cast<FDivExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fde->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fde->right, width_out));
            assert(*width_out != 1 && "uncanonicalized FDiv");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_DIV, {getRoundingModeSort(fde->roundingMode), left, right});
        }

        case Expr::FRem: {
            FRemExpr *fre = cast<FRemExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fre->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fre->right, width_out));
            assert(*width_out != 1 && "uncanonicalized FRem");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_REM, {left, right});
        }

        case Expr::FMax: {
            FMaxExpr *fme = cast<FMaxExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fme->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fme->right, width_out));
            assert(*width_out != 1 && "uncanonicalized FMax");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_MAX, {left, right});
        }

        case Expr::FMin: {
            FMinExpr *fme = cast<FMinExpr>(e);
            cvc5::Term left = castBvToFloat(construct(fme->left, width_out));
            cvc5::Term right = castBvToFloat(construct(fme->right, width_out));
            assert(*width_out != 1 && "uncanonicalized FMin");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_MIN, {left, right});
        }

        // CVC5 API does not need roundingMode?
        case Expr::FRint: {
            FRintExpr *fre = cast<FRintExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(fre->expr, width_out));
            assert(*width_out != 1 && "uncanonicalized FRint");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_RTI, {getRoundingModeSort(fre->roundingMode), arg});
        }

        case Expr::FAbs: {
            FAbsExpr *fae = cast<FAbsExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(fae->expr, width_out));
            assert(*width_out != 1 && "uncanonicalized FAbs");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_ABS, {arg});
        }

        case Expr::FNeg: {
            FNegExpr *fne = cast<FNegExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(fne->expr, width_out));
            assert(*width_out != 1 && "uncanonicalized FNeg");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_NEG, {arg});
        }

        case Expr::FSqrt: {
            FSqrtExpr *fse = cast<FSqrtExpr>(e);
            cvc5::Term arg = castBvToFloat(construct(fse->expr, width_out));
            assert(*width_out != 1 && "uncanonicalized FSqrt");
            return tm.mkTerm(cvc5::Kind::FLOATINGPOINT_SQRT, {getRoundingModeSort(fse->roundingMode), arg});
        }

#if 0
        case Expr::Ne:
        case Expr::Ugt:
        case Expr::Uge:
        case Expr::Sgt:
        case Expr::Sge:
#endif
        default:
            assert(0 && "unhandled Expr type");
            return getTrue();
    }
}

cvc5::Term CVC5Builder::construct(ref<Expr> e, int *width_out) {
  // Apply same optimization strategy as Z3Builder:
  // Skip cache for constant expressions (they're fast to construct)
  // TODO: add a flag to control this behavior
  if (isa<ConstantExpr>(e)) {
    return constructActual(e, width_out);
  } else {
    ExprHashMap<std::pair<cvc5::Term, unsigned>>::iterator it = constructed.find(e);
    if (it != constructed.end()) {
      if (width_out)
        *width_out = it->second.second;
      return it->second.first;
    } else {
      int width;
      if (!width_out)
        width_out = &width;
      cvc5::Term res = constructActual(e, width_out);
      constructed.insert(std::make_pair(e, std::make_pair(res, *width_out)));
      return res;
    }
  }
}

cvc5::Term CVC5Builder::getInitialArray(const Array *root) {
  assert(root);
  cvc5::Term array_expr;
  bool hashed = _arr_hash.lookupArrayExpr(root, array_expr);
  
  if (!hashed) {
    // Unique arrays by name, so we make sure the name is unique by
    // using the size of the array hash as a counter.
    std::string unique_id = std::to_string(_arr_hash._array_hash.size());
    // Prefix unique ID with '_' to avoid name collision if name ends with
    // number
    std::string unique_name = root->name + "_" + unique_id;
    
    cvc5::Sort indexType = getBvSort(root->getDomain());
    cvc5::Sort valueType = getBvSort(root->getRange());
    cvc5::Sort arrayType = getArraySort(indexType, valueType);
    array_expr = tm.mkConst(arrayType, unique_name);

    if (root->isConstantArray() && constant_array_assertions.count(root) == 0) {
      std::vector<cvc5::Term> array_assertions;
      for (unsigned i = 0, e = root->size; i != e; ++i) {
        // construct(= (select i root) root->value[i]) to be asserted in
        // CVC5Solver.cpp
        int width_out;
        cvc5::Term array_value = construct(root->constantValues[i], &width_out);
        assert(width_out == (int)root->getRange() &&
               "Value doesn't match root range");
        array_assertions.push_back(
            eqExpr(readExpr(array_expr, bvConst32(root->getDomain(), i)),
                   array_value));
      }
      constant_array_assertions[root] = std::move(array_assertions);
    }
    
    _arr_hash.hashArrayExpr(root, array_expr);
  }
  
  return array_expr;
}

cvc5::Term CVC5Builder::getArrayForUpdate(const Array *root, const UpdateNode *un) {
  // Iterate over the update nodes, until we find a cached version of the node,
  // or no more update nodes remain
  cvc5::Term un_expr;
  std::vector<const UpdateNode *> update_nodes;
  for (; un && !_arr_hash.lookupUpdateNodeExpr(un, un_expr);
       un = un->next.get()) {
    update_nodes.push_back(un);
  }
  if (!un) {
    un_expr = getInitialArray(root);
  }
  // `un_expr` now holds an expression for the array - either from cache or by
  // virtue of being the initial array expression

  // Create and cache solver expressions based on the update nodes starting from
  // the oldest
  for (const auto &un :
       llvm::make_range(update_nodes.crbegin(), update_nodes.crend())) {
    un_expr =
        writeExpr(un_expr, construct(un->index, 0), construct(un->value, 0));

    _arr_hash.hashUpdateNodeExpr(un, un_expr);
  }

  return un_expr;
}

cvc5::Term CVC5Builder::getInitialRead(const Array *root, unsigned index) {
    return readExpr(getInitialArray(root), bvConst32(32, index));
}

cvc5::Term CVC5Builder::buildArray(const char *name, unsigned indexWidth, unsigned valueWidth) {
    cvc5::Sort indexType = getBvSort(indexWidth);
    cvc5::Sort valueType = getBvSort(valueWidth);
    cvc5::Sort arrayType = getArraySort(indexType, valueType);
    return tm.mkConst(arrayType, name);
}

#endif