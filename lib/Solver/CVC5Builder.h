//===-- CVC5Builder.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CVC5BUILDER_H
#define KLEE_CVC5BUILDER_H

#include "klee/Config/config.h"
#include "klee/Expr/ArrayExprHash.h"
#include "klee/Expr/ExprHashMap.h"

#include <cvc5/cvc5.h>
#include <unordered_map>

namespace klee {

class CVC5ArrayExprHash : public ArrayExprHash<cvc5::Term> {
  friend class CVC5Builder;

public:
  CVC5ArrayExprHash();
  ~CVC5ArrayExprHash() override;
  void clear();
  void clearUpdates();
};

class CVC5Builder {
private:
  void FPCastWidthAssert(int *width_out, char const* msg);
protected:
  cvc5::Term bvOne(unsigned width);
  cvc5::Term bvZero(unsigned width);
  cvc5::Term bvMinusOne(unsigned width);
  cvc5::Term bvConst32(unsigned width, uint32_t value);
  cvc5::Term bvConst64(unsigned width, uint64_t value);

  cvc5::Term bvBoolExtract(const cvc5::Term& expr, int bit);
  cvc5::Term bvExtract(const cvc5::Term& expr, unsigned top, unsigned bottom);
  cvc5::Term eqExpr(const cvc5::Term& a, const cvc5::Term& b);

  // logical left and right shift (not arithmetic)
  cvc5::Term bvLeftShift(const cvc5::Term& expr, unsigned shift);
  cvc5::Term bvRightShift(const cvc5::Term& expr, unsigned shift);
  cvc5::Term bvVarLeftShift(const cvc5::Term& expr, const cvc5::Term& shift);
  cvc5::Term bvVarRightShift(const cvc5::Term& expr, const cvc5::Term& shift);
  cvc5::Term bvVarArithRightShift(const cvc5::Term& expr, const cvc5::Term& shift);

  cvc5::Term notExpr(const cvc5::Term& expr);
  cvc5::Term andExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term orExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term iffExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);

  cvc5::Term bvNotExpr(const cvc5::Term& expr);
  cvc5::Term bvAndExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term bvOrExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term bvXorExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term bvSignExtend(const cvc5::Term& src, unsigned width);

  cvc5::Term constructAShrByConstant(const cvc5::Term& expr, unsigned shift, const cvc5::Term& isSigned);

  cvc5::Term writeExpr(const cvc5::Term& array, const cvc5::Term& index, const cvc5::Term& value);
  cvc5::Term readExpr(const cvc5::Term& array, const cvc5::Term& index);

  cvc5::Term iteExpr(const cvc5::Term& condition, const cvc5::Term& whenTrue, const cvc5::Term& whenFalse);

  cvc5::Term bvLtExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term bvLeExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term sbvLtExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);
  cvc5::Term sbvLeExpr(const cvc5::Term& lhs, const cvc5::Term& rhs);

  cvc5::Term getInitialArray(const Array *os);
  cvc5::Term getArrayForUpdate(const Array *root, const UpdateNode *un);

  cvc5::Term constructActual(ref<Expr> e, int *width_out);
  cvc5::Term construct(ref<Expr> e, int *width_out);

  cvc5::Term buildArray(const char *name, unsigned indexWidth,
                        unsigned valueWidth);
  
  cvc5::Sort getBvSort(unsigned width);
  cvc5::Sort getArraySort(cvc5::Sort domainSort, cvc5::Sort rangeSort);

  std::vector<uint32_t> getFPExpAndSignFromBitWidth(unsigned bitWidth);
  cvc5::Sort getFloatSortFromBitWidth(unsigned bitWidth);
  cvc5::Term getRoundingModeSort(llvm::APFloat::roundingMode rm);

  cvc5::Term castBvToFloat(const cvc5::Term& e);
  cvc5::Term castFPToBitVector(const cvc5::Term& e);

  // cvc5::Solver& slv;
  cvc5::TermManager& tm;
  ExprHashMap<std::pair<cvc5::Term, unsigned>> constructed;
  CVC5ArrayExprHash _arr_hash;
  bool autoClearConstructCache;
  
public:
  std::unordered_map<const Array *, std::vector<cvc5::Term>> constant_array_assertions;
  std::map<cvc5::Term, cvc5::Term> fpToBvAssertions;

  CVC5Builder(cvc5::TermManager& termManager, bool autoClearConstructCache);
  ~CVC5Builder();

  cvc5::Term getTrue();
  cvc5::Term getFalse();
  cvc5::Term getInitialRead(const Array *root, unsigned index);

  cvc5::Term construct(ref<Expr> e) {
    cvc5::Term res = construct(e, nullptr);
    if (autoClearConstructCache)
      clearConstructCache();
    return res;
  }
  
  void clearConstructCache() { constructed.clear(); }
};

} // namespace klee

#endif /* KLEE_CVC5BUILDER_H */