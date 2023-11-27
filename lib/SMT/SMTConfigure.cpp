#include <llvm/Support/CommandLine.h>
#include "z3++.h"
#include "SMT/SMTConfigure.h"

int SMTConfigure::Timeout;
static llvm::cl::opt<int, true> SolverTimeOut("solver-timeout",
		llvm::cl::desc(
				"Set the timeout (ms) of the smt solver. The default value is 10000ms (i.e. 10s)."),
		llvm::cl::location(SMTConfigure::Timeout), llvm::cl::init(10000));

void SMTConfigure::init(int T) {
	if (T != -1 && SolverTimeOut.getNumOccurrences() == 0) {
		Timeout = T;
	}
}
