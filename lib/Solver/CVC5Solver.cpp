//===-- CVC5Solver.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/config.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/FileHandling.h"
#include "klee/Support/OptionCategories.h"

#include <csignal>
#include <sstream>

#ifdef ENABLE_CVC5

#include "CVC5Solver.h"
#include "CVC5Builder.h"

#include "klee/Expr/Constraints.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverImpl.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/ErrorHandling.h"

#include <memory>

#include <cvc5/cvc5.h>

#include <set> 

namespace {
  llvm::cl::opt<unsigned> CVC5VerbosityLevel(
      "debug-cvc5-verbosity", llvm::cl::init(0),
      llvm::cl::desc("CVC5 verbosity level (default=0)"),
      llvm::cl::cat(klee::SolvingCat));

  llvm::cl::opt<std::string> CVC5QueryDumpFile(
    "debug-cvc5-dump-queries", llvm::cl::init(""),
    llvm::cl::desc("Dump CVC5's representation of the query to the specified path"),
    llvm::cl::cat(klee::SolvingCat));

  llvm::cl::opt<bool> CVC5ValidateModels(
      "debug-cvc5-validate-models", llvm::cl::init(false),
      llvm::cl::desc("When generating CVC5 models validate these against the query"),
      llvm::cl::cat(klee::SolvingCat));
}

namespace klee {

class CVC5SolverImpl : public SolverImpl {
private:
  std::unique_ptr<CVC5Builder> builder;
  cvc5::Solver *solver;
  time::Span timeout;
  SolverRunStatus runStatusCode;
  std::unique_ptr<llvm::raw_fd_ostream> dumpedQueriesFile;

  bool internalRunSolver(const Query &,
                        const std::vector<const Array *> *objects,
                        std::vector<std::vector<unsigned char> > *values,
                        bool &hasSolution);
  
  bool validateCVC5Model(cvc5::Term &theModel);

  void addFPCastAssertions(const std::vector<cvc5::Term>& terms);
  void collectAndAddFPCastAssertions(const cvc5::Term& t, std::set<cvc5::Term>& visited);
  
public:
  CVC5SolverImpl();
  ~CVC5SolverImpl();
  void setCoreSolverTimeout(time::Span _timeout) {
    timeout = _timeout;
    
    // Convert timeout from microseconds to milliseconds
    auto timeoutInMilliSeconds = static_cast<unsigned>((timeout.toMicroseconds() / 1000));
    if (timeoutInMilliSeconds == 0) {
      timeoutInMilliSeconds = UINT_MAX;
    }
    std::string timeoutStr = std::to_string(timeoutInMilliSeconds);
    solver->setOption("tlimit-per", timeoutStr);
  }

  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution);

  SolverRunStatus
  handleSolverResponse(cvc5::Result satisfiable,
                       const std::vector<const Array *> *objects,
                       std::vector<std::vector<unsigned char> > *values,
                       bool &hasSolution);
  
  SolverRunStatus getOperationStatusCode();

};

CVC5SolverImpl::CVC5SolverImpl() : runStatusCode(SOLVER_RUN_STATUS_FAILURE) {
  solver = new cvc5::Solver();
  solver->setOption("produce-models", "true");
  solver->setOption("incremental", "true");
  solver->setOption("produce-unsat-cores", "true");
  solver->setLogic("QF_FPABV");
  builder = std::unique_ptr<CVC5Builder>(
      new CVC5Builder(solver->getTermManager(), /*autoClearConstructCache=*/true));
  assert(builder && "CVC5Builder creation failed");

  if (!CVC5QueryDumpFile.empty()) {
    std::string error;
    dumpedQueriesFile = klee_open_output_file(CVC5QueryDumpFile, error);
    if (!dumpedQueriesFile) {
      klee_error("Error creating file for dumping CVC5 queries: %s", error.c_str());
    }
    klee_message("Dumping CVC5 queries to \"%s\"", CVC5QueryDumpFile.c_str());
  }

  // Timeout will be set via setCoreSolverTimeout if needed

  // Set verbosity
  if (CVC5VerbosityLevel > 0) {
    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    ss << CVC5VerbosityLevel;
    ss.flush();
    solver->setOption("verbosity", underlyingString);
  }
}

CVC5SolverImpl::~CVC5SolverImpl() {
  delete solver;
}

CVC5Solver::CVC5Solver() : Solver(std::make_unique<CVC5SolverImpl>()) {}

void CVC5Solver::setCoreSolverTimeout(time::Span _timeout) {
  impl->setCoreSolverTimeout(_timeout);
}

bool CVC5SolverImpl::computeTruth(const Query &query, bool &isValid) {
  bool hasSolution = false; // to remove compiler warning
  bool status =
      internalRunSolver(query, /*objects=*/NULL, /*values=*/NULL, hasSolution);
  isValid = !hasSolution;
  return status;
}

bool CVC5SolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  // Find the object used in the expression, and compute an assignment
  // for them.
  findSymbolicObjects(query.expr, objects);
  if (!computeInitialValues(query.withFalse(), objects, values, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  Assignment a(objects, values);
  result = a.evaluate(query.expr);

  return true;
}

bool CVC5SolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  return internalRunSolver(query, &objects, &values, hasSolution);
}

bool CVC5SolverImpl::internalRunSolver(
    const Query &query, const std::vector<const Array *> *objects,
    std::vector<std::vector<unsigned char> > *values, bool &hasSolution) {

  TimerStatIncrementer t(stats::queryTime);
  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  solver->push();

  // Process constraints in the query
  ConstantArrayFinder constant_arrays_in_query;
  for (auto const &constraint : query.constraints) {
    cvc5::Term constraintTerm = builder->construct(constraint);
    solver->assertFormula(constraintTerm);
    constant_arrays_in_query.visit(constraint);
  }
  ++stats::solverQueries;
  if (objects)
    ++stats::queryCounterexamples;

  // Build the query expression
  cvc5::Term cvc5QueryExpr = builder->construct(query.expr);
  constant_arrays_in_query.visit(query.expr);

  // Process constant array assertions
  for (auto const &constant_array : constant_arrays_in_query.results) {
    assert(builder->constant_array_assertions.count(constant_array) == 1 &&
           "Constant array found in query, but not handled by CVC5Builder");
    for (auto const &arrayIndexValueExpr :
         builder->constant_array_assertions[constant_array]) {
      solver->assertFormula(arrayIndexValueExpr);
    }
  }

  // Add fp to bv assertions
  std::vector<cvc5::Term> allTerms = solver->getAssertions();
  allTerms.push_back(cvc5QueryExpr);
  addFPCastAssertions(allTerms);

  // KLEE queries are validity queries, i.e., ∀ X Constraints(X) → query(X)
  // But CVC5 works with satisfiability, so we query the negation of the equivalent, i.e.,
  // ∃ X Constraints(X) ∧ ¬ query(X)
  cvc5::Term negatedQuery = solver->getTermManager().mkTerm(cvc5::Kind::NOT, {cvc5QueryExpr});
  solver->assertFormula(negatedQuery);

  if (dumpedQueriesFile) {
    *dumpedQueriesFile << "; start CVC5 query\n";
    *dumpedQueriesFile << "(set-logic QF_FPABV)\n";
    // *dumpedQueriesFile << solver->getOutput("raw-benchmark").str();
    *dumpedQueriesFile << "(check-sat)\n";
    *dumpedQueriesFile << "; end CVC5 query\n\n";
    dumpedQueriesFile->flush();
  }

  // Check satisfiability
  cvc5::Result satisfiable = solver->checkSat();
  runStatusCode = handleSolverResponse(satisfiable, objects, values, hasSolution);

  solver->pop();

  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE ||
      runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE) {
    if (hasSolution) {
      ++stats::queriesInvalid;
    } else {
      ++stats::queriesValid;
    }
    return true; // success
  }
  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED) {
    raise(SIGINT);
  }
  return false; // failure
}

SolverImpl::SolverRunStatus CVC5SolverImpl::handleSolverResponse(
    cvc5::Result satisfiable,
    const std::vector<const Array *> *objects,
    std::vector<std::vector<unsigned char> > *values,
    bool &hasSolution) {

  if (satisfiable.isSat()) {
    hasSolution = true;
    if (!objects) {
      // No assignment needed
      assert(values == NULL);
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }
    assert(values && "values cannot be nullptr");
    
    // Get the model
    cvc5::Term theModel = solver->getValue(solver->mkBoolean(true));
    
    values->reserve(objects->size());
    for (std::vector<const Array *>::const_iterator it = objects->begin(),
                                                  ie = objects->end();
         it != ie; ++it) {
      const Array *array = *it;
      std::vector<unsigned char> data;

      data.reserve(array->size);
      for (unsigned offset = 0; offset < array->size; offset++) {
        cvc5::Term initial_read = builder->getInitialRead(array, offset);
        cvc5::Term arrayElementExpr = solver->getValue(initial_read);
        
        // Ensure the retrieved value is a number
        assert(arrayElementExpr.getKind() == cvc5::Kind::CONST_BITVECTOR &&
               "Evaluated expression has wrong sort");

        // Extract integer value from bit vector
        std::string bvStr = arrayElementExpr.getBitVectorValue();
        int arrayElementValue = std::stoi(bvStr, nullptr, 2);
        
        assert(arrayElementValue >= 0 && arrayElementValue <= 255 &&
               "Integer from model is out of range");
        data.push_back(arrayElementValue);
      }
      values->push_back(data);
    }

    // Validate the model if needed
    if (CVC5ValidateModels) { // Can add an option to control whether to validate the model
      bool success = validateCVC5Model(theModel);
      if (!success)
        abort();
    }

    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  } else if (satisfiable.isUnsat()) {
    hasSolution = false;
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  } else {
    assert(satisfiable.isUnknown() && "unhandled solver result");
    cvc5::UnknownExplanation reason = satisfiable.getUnknownExplanation();
    switch (reason) {
    case cvc5::UnknownExplanation::INTERRUPTED:
      return SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED;
    case cvc5::UnknownExplanation::TIMEOUT:
      return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
    default:
      return SolverImpl::SOLVER_RUN_STATUS_FAILURE;
    }
  }
}

bool CVC5SolverImpl::validateCVC5Model(cvc5::Term &theModel) {
  bool success = true;
  
  // Get all assertions
  std::vector<cvc5::Term> assertions = solver->getAssertions();
  
  for (const auto &constraint : assertions) {
    // Evaluate constraint in the model
    cvc5::Term evaluatedExpr = solver->getValue(constraint);
    
    // Check if the evaluation result is true
    if (!evaluatedExpr.isBooleanValue() || !evaluatedExpr.getBooleanValue()) {
      llvm::errs() << "Validating model failed:\n"
                   << "The expression evaluated to false but should be true\n";
      success = false;
    }
  }

  if (!success) {
    llvm::errs() << "Model validation failed\n";
    // Can add more debug information output
  }

  return success;
}

void CVC5SolverImpl::collectAndAddFPCastAssertions(const cvc5::Term& t, std::set<cvc5::Term>& visited) {
    if (visited.count(t)) return;
    visited.insert(t);
    auto it = builder->fpToBvAssertions.find(t);
    if (it != builder->fpToBvAssertions.end()) {
        solver->assertFormula(it->second);
    }
    for (size_t i = 0; i < t.getNumChildren(); ++i) {
        collectAndAddFPCastAssertions(t[i], visited);
    }
}

void CVC5SolverImpl::addFPCastAssertions(const std::vector<cvc5::Term>& terms) {
    std::set<cvc5::Term> visited;
    for (const auto& t : terms) {
        collectAndAddFPCastAssertions(t, visited);
    }
}

SolverImpl::SolverRunStatus CVC5SolverImpl::getOperationStatusCode() { return runStatusCode; }
} // namespace klee

#endif // ENABLE_CVC5