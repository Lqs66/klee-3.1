//===-- CoreSolver.cpp ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "CVC5Solver.h"
#include "STPSolver.h"
#include "Z3Solver.h"
#include "MetaSMTSolver.h"

#include "klee/Solver/SolverCmdLine.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Solver/Solver.h"

#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <memory>

namespace klee {

std::unique_ptr<Solver> createCoreSolver(CoreSolverType cst) {
  switch (cst) {
  case STP_SOLVER:
#ifdef ENABLE_STP
    klee_message("Using STP solver backend");
    return std::make_unique<STPSolver>(UseForkedCoreSolver, CoreSolverOptimizeDivides);
#else
    klee_message("Not compiled with STP support");
    return NULL;
#endif
  case METASMT_SOLVER:
#ifdef ENABLE_METASMT
    klee_message("Using MetaSMT solver backend");
    return createMetaSMTSolver();
#else
    klee_message("Not compiled with MetaSMT support");
    return NULL;
#endif
  case DUMMY_SOLVER:
    return createDummySolver();
  case Z3_SOLVER:
#ifdef ENABLE_Z3
    klee_message("Using Z3 solver backend");
#ifdef ENABLE_FP
    klee_message("Using Z3 bitvector builder");
    return std::make_unique<Z3Solver>(KLEE_BITVECTOR);
#else
    klee_message("Using Z3 core builder");
    return std::make_unique<Z3Solver>(KLEE_CORE);
#endif
#else
    klee_message("Not compiled with Z3 support");
    return NULL;
#endif
  case CVC5_SOLVER:
#ifdef ENABLE_CVC5
    klee_message("Using CVC5 solver backend");
#ifdef ENABLE_FP
    return std::make_unique<CVC5Solver>();
#else
    klee_message("CVC5 must be used with floating-point support enabled");
    return NULL;
#endif
#else
    klee_message("Not compiled with CVC5 support");
    return NULL;
#endif
  case NO_SOLVER:
    klee_message("Invalid solver");
    return NULL;
  default:
    llvm_unreachable("Unsupported CoreSolverType");
  }
}
}
