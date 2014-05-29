#ifndef DVAR
#define DVAR

using namespace std;

class dvariable{
public:
	dvariable(Dwarf_Debug dbg, Dwarf_Die die_var, vector<location *> frame_base);
	dvariable(dvariable &source);//copy from source
	void print_dvar();
	virtual void print_me(){};
	bool cmp_type(dvariable *input);
	virtual ~dvariable(){};
	bool cmp_loc(Exp *exp, address_t pc);
	bool cmp_reg(Exp *exp, address_t pc);

	DVAR_TYPE_T original_type();

	/*information that available in variable DIE or DIEs before typeDIE*/
	string var_name;
	string type_name;
	Dwarf_Off var_type; // the offset of type die of this variable, no matter its base/struc/array/ptr
	vector<location *> loclist;

	/*information that available after we get the typeDIE*/
	/*initialized in dvariable(), set in constructors of other types*/
	int s_offset; // 0 by default, offset if in structure
	DVAR_TYPE_T var_struct_type;//DVAR_UN by default
	dvariable *parent;// 0(NULL) by default
	bool leaf;//whether this is a leaf node in debugging info tree
};

class dbase: public dvariable{
public:
	dbase(dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent);
	void print_me();
	bool libdbg;	//whether this variable is "infered" directly from libc

	Dwarf_Unsigned var_length;
	sign_type_t original_su;
	//sign_type_t infered_su;
};

class dstruct: public dvariable{
public:
	dstruct(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent);
	void print_me();

	Dwarf_Unsigned struct_length;
	vector<dvariable *> member_list;
};

class darray: public dvariable{
public:
	darray(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent);
	void print_me();

	int array_size;
	dvariable *var;
};

class dptr: public dvariable{
public:
	dptr(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent);
	void print_me();
	bool cmp_ptr_type(dptr *input);


	dvariable *var;
};

class subprogram{
public:
	subprogram(Dwarf_Debug dbg, Dwarf_Die die_subprog);
	void print_subprogram();

	vector<dvariable *> var_list;
	vector<location *> frame_base;
	string name;
};

class program{
public:
	program(Dwarf_Debug dbg);
	void print_program();

	vector<subprogram *> func_list;
	vector<dvariable *> global_var_list;
};

#endif
