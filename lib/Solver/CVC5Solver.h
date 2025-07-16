//===-- CVC5Solver.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CVC5SOLVER_H
#define KLEE_CVC5SOLVER_H

#include "klee/Solver/Solver.h"

namespace klee {

/// CVC5Solver - A solver interface for CVC5. This class follows the PImpl
/// (pointer to implementation) idiom to hide CVC5-specific details from
/// the header file, reducing compilation dependencies.
class CVC5Solver : public Solver {
public:
  /// @brief Create a new CVC5-backed solver.
  CVC5Solver();

  void setCoreSolverTimeout(time::Span timeout);

private:
  /// @brief The pointer to the actual implementation.
  class CVC5SolverImpl *impl;
};

} // namespace klee

#endif /* KLEE_CVC5SOLVER_H */
