#ifndef TMP_S_H_
#define TMP_S_H_

using namespace std;



class Tmp_s: public Temp {
public:
	Tmp_s(Temp *tmp, int id);
	Tmp_s(reg_t typ, string name, int id);
	virtual void accept(IRVisitor *v) {
	}
	;

	virtual Tmp_s *clone() const;

	virtual ~Tmp_s() {
	}
	;
	string tostring() const;
	static void destroy(Tmp_s *expr);
	bool cmp_tmp(Tmp_s *tmp);

	int index;
};

class Phi_s: public Exp {
public:
	Phi_s(string phi_name, vector<Tmp_s*> vars);
	virtual ~Phi_s() {};
	void addVar(Tmp_s* e);
	int check_duplicate_para(int dup);
	virtual string tostring() const;
	virtual Phi_s *clone() const;
	virtual void accept(IRVisitor *v) {
	}
	static void destroy(Phi_s *expr);
	vector<Tmp_s*> vars;		/// Phi_s arguments.
	string phi_name; /// The original name for these Phi_s variables.
};


bool is_tmps(Exp *input);
#endif /* EXP_S_H_ */
