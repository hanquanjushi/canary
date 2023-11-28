#include <memory>
// #include "Support/RecursiveTimer.h"
// #include "Support/Statistics.h"
#include "SMT/SMTSolver.h"
#include "SMT/SMTFactory.h"
using namespace std;

// using namespace llvm;

// static cl::opt<std::string> InputFilename(cl::Positional,
//		cl::desc("<input SMT file>"), cl::init("-"),
//		cl::value_desc("filename"));


int main(int argc, char **argv) {
	SMTFactory Ft;
	SMTSolver Sol = Ft.createSMTSolver();
	Sol.add(Ft.parseSMTLib2File(argv[1]));
	std::cout << Sol.check() << std::endl;
	return 0;
}

