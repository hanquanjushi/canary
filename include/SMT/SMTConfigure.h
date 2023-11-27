#ifndef SMT_SMTCONFIGURE_H
#define SMT_SMTCONFIGURE_H

class SMTConfigure {
public:
	static int Timeout;

	// static std::string Tactic;

public:
	static void init(int Timeout);
};

#endif
