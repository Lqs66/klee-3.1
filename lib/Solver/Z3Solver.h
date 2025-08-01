//===-- Z3Solver.h
//---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_Z3SOLVER_H
#define KLEE_Z3SOLVER_H

#include "klee/Solver/Solver.h"

namespace klee {
enum Z3BuilderType {
    KLEE_CORE,
    KLEE_BITVECTOR
};

/// Z3Solver - A complete solver based on Z3
class Z3Solver : public Solver {
public:
  /// Z3Solver - Construct a new Z3Solver.
  Z3Solver(Z3BuilderType type);

  /// Get the query in SMT-LIBv2 format.
  /// \return A C-style string. The caller is responsible for freeing this.
  std::string getConstraintLog(const Query &) override;

  /// setCoreSolverTimeout - Set constraint solver timeout delay to the given
  /// value; 0
  /// is off.
  virtual void setCoreSolverTimeout(time::Span timeout);
};
}

#endif /* KLEE_Z3SOLVER_H */
