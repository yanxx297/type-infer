#ifndef LOCATION
#define LOCATION



using namespace std;

#define WORD_32 4

Dwarf_Small handle_dwop(Dwarf_Small input, int number);
BOOL dwop_to_regname(Dwarf_Small input, string &ret);



class location{
public:
	location(LOC_TYPE_T type, address_t high, address_t low, int p_offset);
	location(location *source);
	virtual BOOL loc_cmp(Exp *exp, address_t addr){return NO;}
	BOOL pc_cmp(address_t addr);
	virtual string tostring(){return "";};
	virtual ~location(){};

	LOC_TYPE_T loc_type;
	address_t low_pc;
	address_t high_pc;

	int piece_offset;//0 by default, for location of a certain piece of structure/array
};

class offset_loc: public location{
public:
	offset_loc(Dwarf_Off original_off, Dwarf_Small original_reg, address_t high, address_t low, int p_offset);
	offset_loc(offset_loc *source);
	BOOL loc_cmp(Exp *exp, address_t addr);
	string tostring();
	virtual ~offset_loc(){};

	Dwarf_Small loc_reg_number;
	string reg_name;
	int offset;
};

class addr_loc: public location{
public:
	addr_loc(Dwarf_Unsigned original_addr, address_t high, address_t low, int p_offset);
	addr_loc(addr_loc *source);
	BOOL loc_cmp(Exp *exp, address_t addr);
	string tostring();
	virtual ~addr_loc(){};

	unsigned long long addr;
};

class reg_loc: public location{
public:
	reg_loc(Dwarf_Small original_reg, address_t high, address_t low, int p_offset);
	reg_loc(reg_loc *source);
	BOOL loc_cmp(Exp *exp, address_t addr);
	string tostring();
	virtual ~reg_loc(){};

	Dwarf_Small store_reg_name;
	string reg_name;
};


#endif
