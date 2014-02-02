#include <stdbool.h>

/*include Vine*/
#include "asm_program.h"
#include "disasm-pp.h"
extern "C"
{
#include "libvex.h"
}
#include "irtoir.h"

#include "dwarf.h"
#include "libdwarf.h"

#include "type_common.h";
#include "location.h"
#include "dvar.h"
#include "tmp_s.h"
#include "vine_api.h";



#include <sstream>

location::location(LOC_TYPE_T type, address_t high, address_t low, int p_offset)
:loc_type(type), high_pc(high), low_pc(low), piece_offset(p_offset)
{}

location::location(location *source)
:loc_type(source->loc_type), high_pc(source->high_pc), low_pc(source->low_pc), piece_offset(source->piece_offset)
{}

bool location::pc_cmp(address_t addr){
	bool result = false;
	if(addr <= this->high_pc && addr >= this->low_pc ){
		result = true;
	}
	return result;
}

bool offset_loc::loc_cmp(Exp *exp, address_t addr){
	bool result = false;
	Tmp_s *t_reg;
	if(exp->exp_type != MEM || this->pc_cmp(addr) == false){
		return result;
	}
	Exp * t_addr = ((Mem *)exp)->addr;
	if(t_addr->exp_type == BINOP){
		//mem[reg + offset]
		//reg is esp or ebp

		BinOp *t_binop = (BinOp *)t_addr;
		int t_off;
		if(is_tmps(t_binop->lhs) == true && t_binop->rhs->exp_type == CONSTANT){
			t_reg = (Tmp_s *)t_binop->lhs;
			t_off = ((Constant *)t_binop->rhs)->val;
		}else if(is_tmps(t_binop->rhs) == true && t_binop->lhs->exp_type == CONSTANT){
			t_reg = (Tmp_s *)t_binop->rhs;
			t_off = ((Constant *)t_binop->lhs)->val;
		}else{
			return result;
		}

		if(this->reg_name == t_reg->name && this->offset == t_off){
			result = true;
			return result;
		}
	}else if(t_addr->exp_type == TEMP){
		//mem[reg], offset is 0

		if(is_tmps(t_addr) == true){
			t_reg = (Tmp_s *)t_addr;
		}else{
			return result;
		}

		if(this->reg_name == t_reg->name){
			result = true;
			return result;
		}
	}

	return result;
}

offset_loc::offset_loc(Dwarf_Off original_off, Dwarf_Small original_reg, address_t high, address_t low, int p_offset)
:location(OFFSET_LOC, high, low, p_offset)
{
	bool result = false;
	string name = "";
	this->loc_reg_number = original_reg;
	this->offset = original_off; //% 18446744069414584320;
	result = dwop_to_regname(this->loc_reg_number, name);
	this->reg_name = name;
}

offset_loc::offset_loc(offset_loc *source)
:location(source->loc_type, source->high_pc, source->low_pc, source->piece_offset), loc_reg_number(source->loc_reg_number), reg_name(source->reg_name), offset(source->offset)
{}

string offset_loc::tostring(){
	stringstream str;
	str<<"offset:"<<this->reg_name<<" "<<this->offset<<" p_off:"<<this->piece_offset;
	string res = str.str();
	return res;
}

bool addr_loc::loc_cmp(Exp *exp, address_t addr){
	bool result = false;
	if(exp->exp_type != MEM || this->pc_cmp(addr) == false){
		return result;
	}

	Exp *t_addr = ((Mem *)exp)->addr;
	if(t_addr->exp_type == CONSTANT){
		Constant *t_con = (Constant *)t_addr;
		if(t_con->val == this->addr){
			result = true;
			return result;
		}
	}

	return result;
}

addr_loc::addr_loc(Dwarf_Unsigned original_addr, address_t high, address_t low, int p_offset)
:location(ADDR_LOC, high, low, p_offset)
{
	this->addr = original_addr;
}

addr_loc::addr_loc(addr_loc *source)
:location(source->loc_type, source->high_pc, source->low_pc, source->piece_offset), addr(source->addr)
{}

string addr_loc::tostring(){
	stringstream str;
	str<<"addr:0x"<<hex<<this->addr<<" p_off:"<<this->piece_offset;
	string res = str.str();
	return res;
}

bool reg_loc::loc_cmp(Exp *exp, address_t addr){
	bool result = false;
	if(this->pc_cmp(addr) == false){
		return result;
	}

	if(is_tmps(exp) == true){
		Tmp_s *t_reg = (Tmp_s *)exp;
		if(t_reg->name == this->reg_name){
			result = true;
			return result;
		}
	}


	return result;
}

reg_loc::reg_loc(Dwarf_Small original_reg, address_t high, address_t low, int p_offset)
:location(REG_LOC, high, low, p_offset)
{
	this->store_reg_name = original_reg;
	if(dwop_to_regname(this->store_reg_name, this->reg_name) == false){
		this->reg_name = "";
	}
}

reg_loc::reg_loc(reg_loc *source)
:location(source->loc_type, source->high_pc, source->low_pc, source->piece_offset), store_reg_name(source->store_reg_name), reg_name(source->reg_name)
{}

string reg_loc::tostring(){
	stringstream str;
	str<<"register:"<<this->reg_name<<" p_off:"<<this->piece_offset;
	string res = str.str();
	return res;
}

bool dwop_to_regname(Dwarf_Small input, string &ret){
	bool result = false;
	int loc = -1;

	if(input >= DW_OP_reg0 && input <= DW_OP_reg31){
		loc = input - DW_OP_reg0;
	}else if(input >= DW_OP_breg0 && input <= DW_OP_breg31){
		loc = input - DW_OP_breg0;
	}

	//cout<<"loc = "<<loc<<endl;
	if(loc != -1){
		ret = str_reg[loc];
		result = true;
	}
	return result;
}



/*Not yet used in functions above*/
//---------------------------------------------------------------------------------------------------X

