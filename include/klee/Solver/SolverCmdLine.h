//===-- SolverCmdLine.h -----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

/*
 * This header groups command-line options and associated declarations
 * that are common to both KLEE and Kleaver.
 */

#ifndef KLEE_SOLVERCMDLINE_H
#define KLEE_SOLVERCMDLINE_H

#include "klee/Config/config.h"
#include "klee/Support/CompilerWarning.h"

DISABLE_WARNING_PUSH
DISABLE_WARNING_DEPRECATED_DECLARATIONS
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/CommandLine.h"
DISABLE_WARNING_POP

#include <set>

namespace klee {

extern llvm::cl::opt<bool> UseFastCexSolver;

extern llvm::cl::opt<bool> UseCexCache;

extern llvm::cl::opt<bool> UseBranchCache;

extern llvm::cl::opt<bool> UseIndependentSolver;

extern llvm::cl::opt<bool> DebugValidateSolver;

extern llvm::cl::opt<std::string> MinQueryTimeToLog;

extern llvm::cl::opt<bool> LogTimedOutQueries;

extern llvm::cl::opt<std::string> MaxCoreSolverTime;

extern llvm::cl::opt<bool> UseForkedCoreSolver;

extern llvm::cl::opt<bool> CoreSolverOptimizeDivides;

extern llvm::cl::opt<bool> UseAssignmentValidatingSolver;

/// The different query logging solvers that can be switched on/off
enum QueryLoggingSolverType {
  ALL_KQUERY,    ///< Log all queries in .kquery (KQuery) format
  ALL_SMTLIB,    ///< Log all queries .smt2 (SMT-LIBv2) format
  SOLVER_KQUERY, ///< Log queries passed to solver in .kquery (KQuery) format
  SOLVER_SMTLIB  ///< Log queries passed to solver in .smt2 (SMT-LIBv2) format
};

extern llvm::cl::bits<QueryLoggingSolverType> QueryLoggingOptions;

enum CoreSolverType {
  STP_SOLVER,
  METASMT_SOLVER,
  DUMMY_SOLVER,
  Z3_SOLVER,
  CVC5_SOLVER,    ///< CVC5
  NO_SOLVER
};

extern llvm::cl::opt<CoreSolverType> CoreSolverToUse;

extern llvm::cl::opt<CoreSolverType> DebugCrossCheckCoreSolverWith;

#ifdef ENABLE_METASMT

enum MetaSMTBackendType {
  METASMT_BACKEND_STP,
  METASMT_BACKEND_Z3,
  METASMT_BACKEND_BOOLECTOR,
  METASMT_BACKEND_CVC4,
  METASMT_BACKEND_YICES2
};

extern llvm::cl::opt<klee::MetaSMTBackendType> MetaSMTBackend;

#endif /* ENABLE_METASMT */

class KCommandLine {
public:
  /// Keep only the options in the provided categories,
  /// together with --help, --help-list, --version and --color
  static void
  KeepOnlyCategories(std::set<llvm::cl::OptionCategory *> const &categories);
};

} // namespace klee

#endif /* KLEE_SOLVERCMDLINE_H */
