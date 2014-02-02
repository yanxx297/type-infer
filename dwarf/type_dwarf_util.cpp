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

#include<vector>

#include "type_common.h"
#include "location.h"
#include "dvar.h"


#include "type_dwarf_util.h"

using namespace std;

//function: check all parents of a given node, to see whether there is any duplicated type
//This function is used to avoid loop
//var is the first parent of given node
dvariable* check_loop_type(dvariable *var, Dwarf_Off type_offset){
	dvariable* res = 0;
	dvariable* buf = var;
	while(buf != 0){
		if(buf != 0 && buf->var_type == type_offset){
			res = buf;
			return res;
		}
		buf = buf->parent;
	}

	return res;
}

bool check_artificial(Dwarf_Die die){
	bool result = false;

	int res;
	Dwarf_Half type_tag;
	Dwarf_Attribute attr;
	Dwarf_Error error = 0;
	Dwarf_Off offset_type;
	Dwarf_Unsigned byte_size;


	/*Get DW_AT_artificial*/
	res = dwarf_attr(die, DW_AT_artificial, &attr, &error);
	if (res == DW_DLV_OK){
		result = true;
		return result;
	}

	return result;
}

bool get_die_name(Dwarf_Die die, string &ret){
	bool result = false;

	char *name = 0;
	Dwarf_Error error = 0;
	int res;

	res = dwarf_diename(die, &name, &error);
	if (res != DW_DLV_OK) {
		perror("Fail to get var name");
		return result;
	}

	ret = std::string(name);
	cout<<"get_die_name:"<<ret<<endl;
	result = true;

	return result;
}

bool get_die_type(Dwarf_Debug dbg, Dwarf_Die die, Dwarf_Die *ret, Dwarf_Off *ret_off){
	/*return the type die of die*/
	bool result = false;
	int res;
	Dwarf_Error error;
	Dwarf_Attribute attr;
	Dwarf_Off offset;
	Dwarf_Half tag;

	Dwarf_Die typeDie = 0;

	/*set default value*/
	*ret_off = 0;
	*ret = 0;

	res = dwarf_attr(die, DW_AT_type, &attr, &error);
	if (res != DW_DLV_OK) {
		perror("cannot get type");
		return result;
	}

	res = dwarf_global_formref(attr, &offset, &error);
	if (res != DW_DLV_OK) {
		perror("fail to get global formref (get_type)");
		return result;
	}

	/*offset -> DIE*/
	res = dwarf_offdie_b(dbg, offset, 1, &typeDie, &error);/*IS info.*/
	if (res != DW_DLV_OK) {
		perror("fail to get dwarf offdie b (get_type)");
		return result;
	}

	/*check whether the type is a typedef*/
	res = dwarf_tag(typeDie, &tag, &error);
	if(res != DW_DLV_OK){
		perror("fail to get tag of type DIE (get_type)");
		return result;
	}
	if(tag == DW_TAG_typedef || tag == DW_TAG_const_type || tag == DW_TAG_subroutine_type){
		result = get_die_type(dbg, typeDie, &typeDie, &offset);
		if(result == false){
			return result;
		}
	}else if(tag == DW_TAG_enumeration_type){
		result = false;
		return result;
	}

	result = true;
	*ret = typeDie;
	*ret_off = offset;
	return result;
}

bool get_die_loclist(Dwarf_Die die, vector<location *> &loc_list, vector<location *> &frame_base){
	bool result = false;
	Dwarf_Locdesc **llbuf;
	Dwarf_Loc *locp;
	int i, j;
	unsigned int entindx;
	Dwarf_Attribute attr;
	Dwarf_Signed count;
	Dwarf_Error error = 0;
	Dwarf_Half tag = 0;
	int res;
	res = dwarf_tag(die, &tag, &error);
	if (res != DW_DLV_OK) {
		perror("var has no tag");
		return result;
	}

	res = dwarf_attr(die, DW_AT_location, &attr, &error);
	if (res != DW_DLV_OK) {
		perror("var has no DW_AT_location");
		return result;
	}

	llbuf = 0;
	res = dwarf_loclist_n(attr, &llbuf, &count, &error);
	//res = dwarf_loclist(attr, &llbuf, &count, &error);
	if (res != DW_DLV_OK) {
		perror("var has no loclist");
		return result;
	}
	//cout<<"find "<<count+1<<" records"<<endl;
	for (j = 0; j < count; j++) {

		unsigned int ents = llbuf[j]->ld_cents;
		//cout<<"\trecord["<<j<<"] has "<<ents<<" DW_OP"<<endl;
		locp = llbuf[j]->ld_s;
		address_t highpc = (address_t)llbuf[j]->ld_hipc;
		address_t lowpc = (address_t)llbuf[j]->ld_lopc;
		int p_offset_count = -1;
		for (entindx = 0; entindx < ents; entindx++) {
			Dwarf_Loc *llocp;
			llocp = locp + entindx;
			Dwarf_Small atom = llocp->lr_atom;
			if(atom == DW_OP_fbreg){
				//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
				//un-handle
				//Look for frame base for fbreg
				int breg_offset = (int)llocp->lr_number;
				for(i = 0; i < frame_base.size(); i++){
					if(frame_base.at(i)->loc_type == OFFSET_LOC){
						offset_loc *fbloc = new offset_loc((offset_loc *)frame_base.at(i));
						fbloc->offset = fbloc->offset + breg_offset;
						loc_list.push_back(fbloc);
					}
				}
			}else if(atom == DW_OP_regx || (atom >= DW_OP_reg0 && atom <= DW_OP_reg31)){
				if(atom == DW_OP_regx){
					atom = handle_dwop(atom, llocp->lr_number);
				}
				Dwarf_Loc *llocp_next;
				llocp_next = locp + entindx + 1;
				Dwarf_Small atom_next = llocp_next->lr_atom;
				if(p_offset_count == -1 && atom_next == DW_OP_piece){
					p_offset_count = 0;
				}
				reg_loc *loc = new reg_loc(atom, highpc, lowpc, p_offset_count);
				loc_list.push_back(loc);
				//cout<<"\tpush record["<<j<<"]"<<endl;
			}else if(atom == DW_OP_bregx || (atom >= DW_OP_breg0 && atom <= DW_OP_breg31)){
				Dwarf_Off breg_offset = 0;
				if(atom == DW_OP_bregx){
					atom = handle_dwop(atom, llocp->lr_number);
					breg_offset = llocp->lr_number2;
				}else{
					breg_offset = llocp->lr_number;
				}
				Dwarf_Loc *llocp_next;
				llocp_next = locp + entindx + 1;
				Dwarf_Small atom_next = llocp_next->lr_atom;
				if(p_offset_count == -1 && atom_next == DW_OP_piece){
					p_offset_count = 0;
				}
				offset_loc *loc = new offset_loc(breg_offset, atom, highpc, lowpc, p_offset_count);
				loc_list.push_back(loc);
				//cout<<"\tpush record["<<j<<"]"<<endl;
			}else if(atom == DW_OP_piece){
				if(p_offset_count == -1){
					p_offset_count = 0;
				}
				p_offset_count += llocp->lr_number;
			}else if(atom == DW_OP_stack_value){
				/*erase all elements with same highPC & lowPC*/
				erase_locrecord(highpc, lowpc, loc_list);
			}
		}
	}

	result = true;
	return result;
}

//-------------------------------------------------------------------------------------------------------X
bool get_frame_base(Dwarf_Die die, vector<location *> &loc_list){
	bool result = false;
	Dwarf_Locdesc **llbuf;
	Dwarf_Loc *locp;
	int i, j;
	unsigned int entindx;
	Dwarf_Attribute attr;
	Dwarf_Signed count;
	Dwarf_Error error = 0;
	Dwarf_Half tag = 0;
	int res;
	res = dwarf_tag(die, &tag, &error);
	if (res != DW_DLV_OK) {
		perror("var has no tag");
		return result;
	}

	res = dwarf_attr(die, DW_AT_frame_base, &attr, &error);
	if (res != DW_DLV_OK) {
		perror("var has no DW_AT_location");
		return result;
	}

	llbuf = 0;
	res = dwarf_loclist_n(attr, &llbuf, &count, &error);
	if (res != DW_DLV_OK) {
		perror("var has no loclist");
		return result;
	}
	for (j = 0; j < count; j++) {

		unsigned int ents = llbuf[j]->ld_cents;
		locp = llbuf[j]->ld_s;
		address_t highpc = (address_t)llbuf[j]->ld_hipc;
		address_t lowpc = (address_t)llbuf[j]->ld_lopc;
		int p_offset_count = -1;
		for (entindx = 0; entindx < ents; entindx++) {
			Dwarf_Loc *llocp;
			llocp = locp + entindx;
			Dwarf_Small atom = llocp->lr_atom;
			if(atom == DW_OP_regx || (atom >= DW_OP_reg0 && atom <= DW_OP_reg31)){
				if(atom == DW_OP_regx){
					atom = handle_dwop(atom, llocp->lr_number);
				}
				Dwarf_Loc *llocp_next;
				llocp_next = locp + entindx + 1;
				Dwarf_Small atom_next = llocp_next->lr_atom;
				if(p_offset_count == -1 && atom_next == DW_OP_piece){
					p_offset_count = 0;
				}
				reg_loc *loc = new reg_loc(atom, highpc, lowpc, p_offset_count);
				loc_list.push_back(loc);
				//cout<<"\tpush record["<<j<<"]"<<endl;
			}else if(atom == DW_OP_bregx || (atom >= DW_OP_breg0 && atom <= DW_OP_breg31)){
				Dwarf_Off breg_offset = 0;
				if(atom == DW_OP_bregx){
					atom = handle_dwop(atom, llocp->lr_number);
					breg_offset = llocp->lr_number2;
				}else{
					breg_offset = llocp->lr_number;
				}
				Dwarf_Loc *llocp_next;
				llocp_next = locp + entindx + 1;
				Dwarf_Small atom_next = llocp_next->lr_atom;
				if(p_offset_count == -1 && atom_next == DW_OP_piece){
					p_offset_count = 0;
				}
				offset_loc *loc = new offset_loc(breg_offset, atom, highpc, lowpc, p_offset_count);
				loc_list.push_back(loc);
			}else if(atom == DW_OP_piece){
				if(p_offset_count == -1){
					p_offset_count = 0;
				}
				p_offset_count += llocp->lr_number;
			}else if(atom == DW_OP_stack_value){
				/*erase all elements with same highPC & lowPC*/
				erase_locrecord(highpc, lowpc, loc_list);
			}
		}
	}

	result = true;
	return result;
}

bool get_die_size(Dwarf_Die typeDie, int *ret){
	bool result;

	int res;
	Dwarf_Half type_tag;
	Dwarf_Attribute attr;
	Dwarf_Error error = 0;
	Dwarf_Off offset_type;
	Dwarf_Unsigned byte_size;

	/*set default*/
	*ret = 0;

	/*Get length*/
	res = dwarf_attr(typeDie, DW_AT_byte_size, &attr, &error);
	if (res != DW_DLV_OK){
		perror("var has no size attr");
		return result;
	}

	res = dwarf_formudata(attr, &byte_size, &error);
	if(res != DW_DLV_OK){
		perror("Fail to get var size, although var has DW_AT_byte_size");
		return result;
	}

	result = true;
	*ret = byte_size;
	return result;
}

bool get_die_offset(Dwarf_Die typeDie, int *ret){
	bool result = false;
	Dwarf_Locdesc *llbuf;
	Dwarf_Loc *locp;
	int i, j;
	unsigned int entindx;
	Dwarf_Attribute attr;
	Dwarf_Signed count;
	Dwarf_Error error = 0;
	int res;
	int offset = -1;

	res = dwarf_attr(typeDie, DW_AT_data_member_location, &attr, &error);
	if (res != DW_DLV_OK) {
		perror("var has no data member location attr");
		exit(1);
	}

	llbuf = 0;
	res = dwarf_loclist(attr, &llbuf, &count, &error);
	if (res != DW_DLV_OK) {
		perror("fail to get loclist of var's data member loc");
		exit(1);
	}
	for (j = 0; j < count; ++j) {
		unsigned int ents = llbuf[j].ld_cents;
		locp = llbuf[j].ld_s;
		for (entindx = 0; entindx < ents; entindx++) {
			Dwarf_Loc *llocp;
			llocp = locp + entindx;
			if(llocp->lr_atom == DW_OP_plus_uconst){
				offset = llocp->lr_number;
				break;
			}
		}
		if(offset != -1){
			break;
		}
	}

	if(offset != -1){
		result = true;
		*ret = offset;
	}
	return result;

}

bool get_die_su(Dwarf_Die typeDie, sign_type_t *ret){
	bool result = false;
	int res;
	Dwarf_Unsigned s_u;
	Dwarf_Attribute attr;
	Dwarf_Error error;

	/*set default*/
	*ret = UNKNOW_T;

	res = dwarf_attr(typeDie, DW_AT_encoding, &attr, &error);
	if (res != DW_DLV_OK) {
		perror("var has no s/u attr");
		return result;
	}
	res = dwarf_formudata(attr, &s_u, &error);
	if (res != DW_DLV_OK) {
		perror("fail to get the value of s/u attr");
		return result;
	}

	if(s_u == DW_ATE_unsigned || s_u == DW_ATE_unsigned_char){
		*ret = UNSIGNED_T;
	}else if(s_u == DW_ATE_signed || s_u == DW_ATE_signed_char){
		*ret = SIGNED_T;
	}else{
		*ret = UNKNOW_T;
	}

	result = true;
	return result;
}

bool get_array_size(Dwarf_Die typeDie, int *ret){
	bool result = false;
	int res = 0;
	Dwarf_Die die_subrange = 0;
	Dwarf_Unsigned array_size;
	Dwarf_Attribute attr;
	Dwarf_Error error = 0;

	/*set default*/
	*ret = 0;

	res = dwarf_child(typeDie,&die_subrange, &error);
	if (res != DW_DLV_OK) {
		return result;
	}

	res = dwarf_attr(die_subrange, DW_AT_upper_bound, &attr, &error);
	if (res != DW_DLV_OK) {
		return result;
	}
	res = dwarf_formudata(attr, &array_size, &error);
	if (res != DW_DLV_OK) {
		return result;
	}
	*ret = ((int)array_size)+1;
	return result;
}
//---------------------------------------------------------------------------------------------------X

//function: get tag of an DIE
bool get_die_tag(Dwarf_Die die, Dwarf_Half *tag){
	int res;
	bool result = false;
	Dwarf_Error error = 0;
	Dwarf_Half buf;

	/*set default*/
	*tag = 0;

	res = dwarf_tag(die, &buf, &error);
	if (res != DW_DLV_OK) {
		perror("No tag for this DIE");
		return result;
	}

	result = true;
	*tag = buf;
	return result;
}

//function: dw_op_(b)regx+num -> de_op_(b)regN
//for example:
//dw_op_bregx+number -> dw_op_breg0~31
//dw_op_regx+number -> dw_op_reg0~31
//para2 is set to -1 if no number
Dwarf_Small handle_dwop(Dwarf_Small input, int number){
	Dwarf_Small res;

	if(input >= DW_OP_reg0 && input <= DW_OP_breg31){
		res = input;
	}else{
		if(number < 0 || number > 31){
			res = 0;
		}else{
			switch(input){
			case DW_OP_regx:{
				res = DW_OP_reg0 + number;
				break;
			}
			case DW_OP_bregx:{
				res = DW_OP_breg0 + number;
				break;
			}
			default:{
				break;
			}
			}
		}
	}

	return res;
}

//function: erase all elements with same highPC & lowPC
void erase_locrecord(address_t highpc, address_t lowpc, vector<location *> &input){
	int i;
	for(i = 0; i < input.size(); i++){
		if(input.at(i)->low_pc == lowpc && input.at(i)->high_pc == highpc){
			vector<location *>::iterator iter = input.begin()+i;
			input.erase(iter);
			i--;
		}
	}
}

//function: remove all loclist records that are not mine
void customize_loclist(dvariable *var){
	int i, j;
	vector<dvariable *>type_stack;
	dvariable *buf = var;
	while(buf != 0){
		type_stack.push_back(buf);
		buf = buf->parent;
	}
	for(i = 0; i < var->loclist.size(); i++){
		int offset = var->loclist.at(i)->piece_offset;
		//cout<<"offset of "<<var->loclist.at(i)->tostring()<<" is "<<offset<<"at begining"<<endl;
		/*piece offset == -1 >> this location adapt for every element in this struct (root location)*/
		if(offset == -1){
			continue;
		}

		for(j = type_stack.size()-1; j >= 0; j--){
			switch(type_stack.at(j)->var_struct_type){
			//cout<<type_stack.at(j)->var_name<<":"<<endl;
			case DVAR_ARRAY:{
				if(type_stack.at(j-1)->var_struct_type != DVAR_ARRAY){
					switch(type_stack.at(j-1)->var_struct_type){
					case DVAR_BASE:{
						dbase * next = (dbase *)type_stack.at(j-1);
						offset = offset % next->var_length;
						//cout<<"\t"<<next->var_name<<":offset mod "<<next->var_length<<endl;
						break;
					}
					case DVAR_STRUCT:{
						dstruct * next = (dstruct *)type_stack.at(j-1);
						offset = offset % next->struct_length;
						//cout<<"\t"<<next->var_name<<":offset - "<<next->struct_length<<endl;
						break;
					}
					case DVAR_POINTER:{
						offset = offset % WORD_32;
						break;
					}
					default:{
						break;
					}
					}
				}
				break;
			}
			case DVAR_STRUCT:{
				//printf("j=%d\n",j);
				offset = offset - type_stack.at(j-1)->s_offset;
				//cout<<"\toffset - "<<type_stack.at(j-1)->s_offset<<endl;
				break;
			}
			default:{
				break;
			}
			}
			if(offset < 0){
				break;
			}
		}
		//cout<<"Final offset of <"<<var->loclist.at(i)->tostring()<<"> for "<<var->var_name<<" is "<<offset<<endl;
		if(offset != 0){
			vector<location *>::iterator iter= var->loclist.begin() + i;
			var->loclist.erase(iter);
			i--;
		}
	}
}

//function: given register name and offset of a variable, return whether its the variable
//represented by var
bool cmp_offset_loc(string regname, int offset, address_t pc, dvariable *var){
	bool result = false;
	int i;

	for(i = 0; i < var->loclist.size(); i++){
		if(var->loclist.at(i)->loc_type == OFFSET_LOC){
			offset_loc * loc = (offset_loc *)var->loclist.at(i);
			if(loc->piece_offset == -1){
				/*non optimization location*/
				/*get var type*/
				int small_off = offset - loc->offset;
				if(small_off >= 0){
					if(loc->reg_name == regname && cmp_offset(small_off, var) == true){
						result = true;
						break;
					}
				}

			}else{
				/*optimization location*/
				/*check PC range*/
				if(loc->pc_cmp(pc) == false){
					continue;
				}
				if(loc->reg_name == regname && offset == loc->offset){
					result = true;
					break;
				}
			}
		}
//		else if(var->loclist.at(i)->loc_type == REG_LOC){
//			//cout<<"compare ("<<regname<<","<<offset<<") and "<<var->loclist.at(i)->tostring()<<endl;
//			reg_loc * loc = (reg_loc *)var->loclist.at(i);
//			if(loc->reg_name == regname && cmp_offset(offset, var) == true){
//				result = true;
//				break;
//			}
//		}
	}

	return result;
}

//function: compare the given inside offset and inside offset of given variable
bool cmp_offset(int in_offset, dvariable *var){
	//cout<<"************************cmp_offset() begin******************************"<<endl;
	//cout<<"IR_offset: "<<in_offset<<endl;
	//cout<<"Variable: "<<var->var_name<<endl;
	bool result = false;
	int i, j;
	vector<dvariable *>type_stack;
	dvariable *buf = var;
	while(buf != 0){
		type_stack.push_back(buf);
		buf = buf->parent;
		if(buf != 0 && buf->var_struct_type == DVAR_POINTER){
			break;
		}
	}

	int offset = in_offset;

	for(j = type_stack.size()-1; j >= 0; j--){
		switch(type_stack.at(j)->var_struct_type){
		case DVAR_ARRAY:{
			int count = 0;
			if(type_stack.at(j-1)->var_struct_type != DVAR_ARRAY){
				switch(type_stack.at(j-1)->var_struct_type){
				case DVAR_BASE:{
					dbase * next = (dbase *)type_stack.at(j-1);
					count = offset / next->var_length;
					offset = offset % next->var_length;
					break;
				}
				case DVAR_STRUCT:{
					dstruct * next = (dstruct *)type_stack.at(j-1);
					count = offset / next->struct_length;
					offset = offset % next->struct_length;
					break;
				}
				case DVAR_POINTER:{
					count = offset / WORD_32;
					offset = offset % WORD_32;
					break;
				}
				default:{
					break;
				}
				}

				/*exceed array size*/
				if(count >= ((darray *)type_stack.at(j))->array_size){
					return result;
				}
			}
			break;
		}
		case DVAR_STRUCT:{
			offset = offset - type_stack.at(j-1)->s_offset;
			break;
		}
		default:{
			break;
		}
		}
		if(offset < 0){
			break;
		}
	}

	if(offset != 0){
		return result;
	}

	//cout<<"offset = variable_off"<<endl;
	result = true;

	return result;
}

int handle_constant(unsigned long long offset){
	int tmp_off = -1;
	if((offset&2147483648) == 0){
		/*positive*/
		tmp_off = (int)offset;
	}else if((offset&2147483648) == 2147483648){
		/*negative*/
		tmp_off = (int)(offset - 4294967296);
	}

	return tmp_off;
}

void handle_child_and_sibling(Dwarf_Debug dbg, Dwarf_Die in_die, vector<dvariable *> &var_list, vector<location *> &frame_base){
	int res = 0;
	bool result = false;
	Dwarf_Die cur_die = 0;
	Dwarf_Error error;

	res = dwarf_child(in_die, &cur_die, &error);
	while(res == DW_DLV_OK){
		/*handle DIE*/
		Dwarf_Half cur_tag = 0;
		get_die_tag(cur_die, &cur_tag);
		switch(cur_tag){
		case DW_TAG_variable:
		case DW_TAG_formal_parameter:{

			/*Build var and push into vector*/
			dvariable *source = new dvariable(dbg, cur_die, frame_base);
			Dwarf_Off off_type_cur = 0;
			Dwarf_Die die_type_cur = 0;
			result = get_die_type(dbg, cur_die, &die_type_cur, &off_type_cur);
			if(result == true && source->var_name!="" && source->loclist.size()>0){
				Dwarf_Half cur_type_tag = 0;
				get_die_tag(die_type_cur, &cur_type_tag);
				switch(cur_type_tag){
				case DW_TAG_base_type:{
					dbase * member = new dbase(*source, die_type_cur, off_type_cur, 0, (dvariable *)0);
					var_list.push_back(member);
					break;
				}
				case DW_TAG_structure_type:{
					dstruct * member = new dstruct(dbg, *source, die_type_cur, off_type_cur, 0, (dvariable *)0);
					var_list.push_back(member);
					break;
				}
				case DW_TAG_array_type:{
					darray * member = new darray(dbg, *source, die_type_cur, off_type_cur, 0, (dvariable *)0);
					var_list.push_back(member);
					break;
				}
				case DW_TAG_pointer_type:{
					dptr * member = new dptr(dbg, *source, die_type_cur, off_type_cur, 0, (dvariable *)0);
					var_list.push_back(member);
					break;
				}
				default:{
					break;
				}
				}
			}
			break;
		}
		default:{
			handle_child_and_sibling(dbg, cur_die, var_list, frame_base);
			break;
		}
		}

		/*switch to next DIE*/
		res = dwarf_siblingof(dbg, cur_die, &cur_die, &error);
	}


}

