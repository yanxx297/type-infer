/*include Vine*/
#include "asm_program.h"
#include "disasm-pp.h"
extern "C"
{
#include "libvex.h"
}
#include "irtoir.h"

/*include libdwarf*/
#include "dwarf.h"
#include "libdwarf.h"

#include "type_common.h"
#include "location.h"
#include "dvar.h"
#include "type_dwarf_util.h"
#include "tmp_s.h"


using namespace std;

dvariable::dvariable(Dwarf_Debug dbg, Dwarf_Die die_var, vector<location *> frame_base)
:s_offset(0), var_struct_type(DVAR_UN), parent(0), leaf(NO){
	BOOL res;
	int res_tag;
	Dwarf_Half tag = 0;
	Dwarf_Die die_type;
	Dwarf_Off off_type;
	string name;

	/*name*/
	get_die_name(die_var, name);
	this->var_name = name;

	/*type offset*/
	get_die_type(dbg, die_var, &die_type, &off_type);
	this->var_type = off_type;

	/*location list*/
	cout<<this->var_name<<" get loc_list:"<<endl;
	get_die_loclist(die_var, this->loclist, frame_base);
}

dvariable::dvariable(dvariable &source){
	int i;

	this->var_name = source.var_name;
	this->var_type = source.var_type;
	this->s_offset = source.s_offset;
	this->var_struct_type = source.var_struct_type;
	this->parent = source.parent;

	if(source.leaf == NO){
		this->leaf == NO;
	}

	for(i = 0; i < source.loclist.size(); i++){
		this->loclist.push_back(source.loclist.at(i));
	}
}

void dvariable::print_dvar(){
	int i;
	switch(this->var_struct_type){
	case DVAR_BASE:{
		cout<<"base:"<<this->var_name<<"("<<this<<")"<<endl;
		break;
	}
	case DVAR_ARRAY:{
		cout<<"array:"<<this->var_name<<"("<<this<<")"<<endl;
		break;
	}
	case DVAR_STRUCT:{
		cout<<"struct:"<<this->var_name<<"("<<this<<")"<<endl;
		break;
	}
	case DVAR_POINTER:{
		cout<<"pointer:"<<this->var_name<<"("<<this<<")"<<endl;
		break;
	}
	default:{
		cout<<"???:"<<this->var_name<<"("<<this<<")"<<endl;
		break;
	}
	}
	if(this->leaf == YES){
		cout<<"Is a Leaf."<<endl;
	}
	cout<<"type off: 0x"<<hex<<this->var_type<<endl;
	cout<<"offset:"<<this->s_offset<<endl;
	cout<<"parent: 0x"<<hex<<this->parent<<endl;

	cout<<"loc_list["<<this->loclist.size()<<"]:"<<endl;
	for(i = 0; i < this->loclist.size(); i++){
		cout<<"\t"<<this->loclist.at(i)->tostring()<<endl;
	}
}

BOOL dvariable::cmp_type(dvariable *input){
	BOOL result = NO;
	if(this->var_type == input->var_type){
		if(this->parent == 0 || input->parent == 0){
			result = YES;
		}else{
			if(this->parent->cmp_type(input->parent) == YES){
				result = YES;
			}
		}
	}
	return result;
}

BOOL dvariable::cmp_loc(Exp *exp, address_t pc){
	//cout<<"\tlook for "<<exp->tostring()<<endl;
	BOOL result = NO;
	if(exp->exp_type != MEM){
		return result;
	}
	Mem *mem = (Mem *)exp;
	if(mem->addr->exp_type == BINOP){
		int offset = 0;
		string regname;
		BinOp * bop = (BinOp *)mem->addr;
		if(bop->lhs->exp_type == TEMP && bop->rhs->exp_type == CONSTANT){
			offset = handle_constant(((Constant *)bop->rhs)->val);
			regname = ((Temp *)bop->lhs)->name;
			if(bop->binop_type == PLUS){
				/*do nothing*/
			}else if(bop->binop_type == MINUS){
				offset = -1 * offset;
			}else{
				/*illegal representation of offset_loc*/
				return result;
			}
		}else if(bop->rhs->exp_type == TEMP && bop->lhs->exp_type == CONSTANT){
			offset = handle_constant(((Constant *)bop->lhs)->val);
			regname = ((Temp *)bop->rhs)->name;
		}else{
			return result;
		}
		if(offset == -1){
			return result;
		}
		if(cmp_offset_loc(regname, offset, pc, this) == YES){
			result = YES;
			//cout<<"\t\tfind "<<this->var_name<<endl;
			return result;
		}
	}else if(mem->addr->exp_type == TEMP){
		string regname;
		Temp *tmp = (Temp *)mem->addr;
		regname = tmp->name;
		if(cmp_offset_loc(regname, 0, pc, this) == YES){
			result = YES;
			return result;
		}
	}else if(mem->addr->exp_type == CONSTANT){
		/*constant address used by global or static*/
		int i;
		for(i = 0; i < this->loclist.size(); i++){
			if(this->loclist.at(i)->loc_type == ADDR_LOC){
				if(this->loclist.at(i)->loc_cmp(mem, pc) == YES){
					result = YES;
					return result;
				}
			}
		}
	}
	return result;
}

BOOL dvariable::cmp_reg(Exp *exp, address_t pc){
	BOOL result = NO;
	int i;
	if(is_tmps(exp) != YES){
		return result;
	}
	Tmp_s *reg = (Tmp_s *)exp;
	for(i = 0; i < this->loclist.size(); i++){
		if(this->loclist.at(i)->loc_type == REG_LOC){
			reg_loc * loc = (reg_loc *)this->loclist.at(i);
			if(reg->name == loc->reg_name && loc->pc_cmp(pc) == YES){
				result = YES;
				break;
			}
		}
	}
	return result;
}

dbase::dbase(dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent)
:dvariable(source)
{
	int i, j;
	int size = 0;
	sign_type_t su_ype = UNKNOW_T;
	string name;

	/*set dvariable*/
	this->s_offset = member_loc;
	//this->infered_su = UNKNOW_T;
	this->var_struct_type = DVAR_BASE;
	this->parent = parent;

	/*set type*/
	this->var_type = off_type;

	/*get length*/
	get_die_size(die_type, &size);
	this->var_length = size;

	/*get original signed/unsigned*/
	get_die_su(die_type, &su_ype);
	this->original_su = su_ype;

	/*customize loc_list*/
	customize_loclist(this);

}

void dbase::print_me(){
	cout<<"*************************"<<endl;
	this->print_dvar();
	cout<<"variable size: "<<this->var_length<<endl;
	if(this->original_su == SIGNED_T){
		cout<<"signed"<<endl;
	}else if(this->original_su == UNSIGNED_T){
		cout<<"unsigned"<<endl;
	}else if(this->original_su == UNKNOW_T){
		cout<<"unknow"<<endl;
	}
	//cout<<"*************************"<<endl;
}


dstruct::dstruct(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent)
:dvariable(source)
{
	int res;
	BOOL res_b;
	int i, j;
	int size = 0;
	Dwarf_Die die_member = 0;
	Dwarf_Half tag_member = 0;
	Dwarf_Error error = 0;

	/*set dvariable*/
	this->s_offset = member_loc;
	this->var_struct_type = DVAR_STRUCT;
	this->parent = parent;

	/*set type*/
	this->var_type = off_type;

	/*get length*/
	get_die_size(die_type, &size);
	this->struct_length = size;

	/*Add members into vector*/
	res = dwarf_child(die_type, &die_member, &error);
	while(res == DW_DLV_OK){
		/*get offset*/
		int offset = 0;
		get_die_offset(die_member, &offset);

		/*get this member, push into vector*/
		get_die_tag(die_member, &tag_member);
		if(tag_member == DW_TAG_member){
			dvariable *member_source = new dvariable(source);

			/*get member name*/
			string member_name;
			get_die_name(die_member, member_name);
			member_source->var_name = member_name;

			Dwarf_Die die_member_type = 0;
			Dwarf_Off off_member_type = 0;
			res_b = get_die_type(dbg, die_member, &die_member_type, &off_member_type);
			if(res_b == YES){
				Dwarf_Half tag_member_type = 0;
				get_die_tag(die_member_type, &tag_member_type);

				/*if not, create a new one*/
				switch(tag_member_type){
				case DW_TAG_base_type:{
					dbase * member = new dbase(*member_source, die_member_type, off_member_type, offset, this);
					this->member_list.push_back(member);
					break;
				}
				case DW_TAG_structure_type:{
					dstruct * member = new dstruct(dbg, *member_source, die_member_type, off_member_type, offset, this);
					this->member_list.push_back(member);
					break;
				}
				case DW_TAG_array_type:{
					darray * member = new darray(dbg, *member_source, die_member_type, off_member_type, offset, this);
					this->member_list.push_back(member);
					break;
				}
				case DW_TAG_pointer_type:{
					dptr * member = new dptr(dbg, *member_source, die_member_type, off_member_type, offset, this);
					this->member_list.push_back(member);
					break;
				}
				default:{
					break;
				}
				}
			}
		}

		/*get next member*/
		res = dwarf_siblingof(dbg, die_member, &die_member, &error);
	}
}

void dstruct::print_me(){
	int i;

	cout<<"*************************"<<endl;
	this->print_dvar();
	cout<<"struct size: "<<this->struct_length<<endl;
	if(this->leaf != YES){
		for(i = 0; i < this->member_list.size(); i++){
			this->member_list.at(i)->print_me();
		}
	}
	//cout<<"*************************"<<endl;
}


darray::darray(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent)
:dvariable(source)
{
	BOOL result = NO;
	int array_size = 0;
	Dwarf_Die die_element_type = 0;
	Dwarf_Off off_element_type = 0;

	/*set dvariable*/
	this->s_offset = member_loc;
	this->var_struct_type = DVAR_ARRAY;
	this->parent = parent;

	/*set type*/
	this->var_type = off_type;

	/*set array size*/
	get_array_size(die_type, &array_size);
	this->array_size = array_size;

	/*set array element (ptr)*/
	result = get_die_type(dbg, die_type, &die_element_type, &off_element_type);
	if(result == YES){
		Dwarf_Half tag_element_type = 0;
		get_die_tag(die_element_type, &tag_element_type);
		switch(tag_element_type){
		case DW_TAG_base_type:{
			dbase * member = new dbase(source, die_element_type, off_element_type, 0, this);
			this->var = member;
			break;
		}
		case DW_TAG_structure_type:{
			dstruct * member = new dstruct(dbg, source, die_element_type, off_element_type, 0, this);
			this->var = member;
			break;
		}
		case DW_TAG_array_type:{
			darray * member = new darray(dbg, source, die_element_type, off_element_type, 0, this);
			this->var = member;
			break;
		}
		case DW_TAG_pointer_type:{
			dptr * member = new dptr(dbg, source, die_element_type, off_element_type, 0, this);
			this->var = member;
			break;
		}
		default:{
			break;
		}
		}
	}
}

void darray::print_me(){
	cout<<"*************************"<<endl;
	this->print_dvar();
	cout<<"array size: "<<this->array_size<<endl;
	if(this->leaf!= YES && this->var != 0){
		this->var->print_me();
	}else{
		cout<<"\tVoid array"<<endl;
	}
	//cout<<"*************************"<<endl;
}

dptr::dptr(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, dvariable *parent)
:dvariable(source)
{
	BOOL result = NO;
	Dwarf_Die die_target_type = 0;
	Dwarf_Off off_target_type = 0;

	/*set dvariable*/
	this->s_offset = member_loc;
	this->var_struct_type = DVAR_POINTER;
	this->parent = parent;

	/*set type*/
	this->var_type = off_type;

	/*customize loc_list*/
	customize_loclist(this);

	/*set pointer's target*/
	result = get_die_type(dbg, die_type, &die_target_type, &off_target_type);
	if(result == YES){
		/*check whether this type already exist in debug_info*/
		dvariable *tmp = check_loop_type(this, off_target_type);
		if(tmp != 0){
			this->var = tmp;
			this->leaf = YES;
			return;
		}

		Dwarf_Half tag_target_type = 0;
		get_die_tag(die_target_type, &tag_target_type);
		switch(tag_target_type){
		case DW_TAG_base_type:{
			dbase * member = new dbase(source, die_target_type, off_target_type, 0, this);

			this->var = member;
			break;
		}
		case DW_TAG_structure_type:{
			dstruct * member = new dstruct(dbg, source, die_target_type, off_target_type, 0, this);
			this->var = member;
			break;
		}
		case DW_TAG_array_type:{
			darray * member = new darray(dbg, source, die_target_type, off_target_type, 0, this);
			this->var = member;
			break;
		}
		case DW_TAG_pointer_type:{
			dptr * member = new dptr(dbg, source, die_target_type, off_target_type, 0, this);
			this->var = member;
			break;
		}
		default:{
			break;
		}
		}
	}else{
		this->var = 0;
	}
}

void dptr::print_me(){
	cout<<"*************************"<<endl;
	this->print_dvar();
	if(this->leaf != YES && this->var != 0){
		this->var->print_me();
	}else{
		if(this->var == 0){
			cout<<"\tvoid pointer\n"<<endl;
		}
	}
	//cout<<"*************************"<<endl;
}

subprogram::subprogram(Dwarf_Debug dbg, Dwarf_Die die_subprog){
	string name;

	/*set subprogram name*/
	get_die_name(die_subprog, name);
	this->name = name;

	/*set frame base*/
	get_frame_base(die_subprog, this->frame_base);

	/*push variables into vector*/
	handle_child_and_sibling(dbg, die_subprog, this->var_list, this->frame_base);
}

program::program(Dwarf_Debug dbg){
	Dwarf_Unsigned cu_header_length = 0;
	Dwarf_Half version_stamp = 0;
	Dwarf_Unsigned abbrev_offset = 0;
	Dwarf_Half address_size = 0;
	Dwarf_Unsigned next_cu_header = 0;
	Dwarf_Error error;

	while(1){
		Dwarf_Die no_die = 0;
		Dwarf_Die cu_die = 0;
		int res = DW_DLV_ERROR;
		res = dwarf_next_cu_header(dbg, &cu_header_length, &version_stamp, &abbrev_offset, &address_size, &next_cu_header, &error);
		if (res == DW_DLV_ERROR) {
			printf("Error in dwarf_next_cu_header\n");
			exit(1);
		}
		if (res == DW_DLV_NO_ENTRY) {
			/* Done. */
			//printf("Done\n");
			return;
		}
		//printf("find new CU\n");
		/* The CU will have a single sibling, a cu_die. */
		res = dwarf_siblingof(dbg, no_die, &cu_die, &error);
		if (res == DW_DLV_ERROR) {
			printf("Error in dwarf_siblingof on CU die \n");
			exit(1);
		}

		/*get all children of cu_die*/
		Dwarf_Die die_cu_child = 0;
		res = dwarf_child(cu_die, &die_cu_child, &error);
		while(res == DW_DLV_OK){
			//printf("\tfind new child:");
			Dwarf_Half child_tag = 0;
			get_die_tag(die_cu_child, &child_tag);
			//printf("%x\n",child_tag);
			switch(child_tag){
			case DW_TAG_subprogram:{
				//printf("\t\tDW_TAG_subprogram\n");
				subprogram * subprog = new subprogram(dbg, die_cu_child);

				/*no name/artificial -> don't push into stack*/
				if(subprog->name == "" || check_artificial(die_cu_child) == YES){
					break;
				}

				this->func_list.push_back(subprog);
				break;
			}
			case DW_TAG_variable:{
				//printf("\t\tDW_TAG_variable\n");
				/*push global variable into stack*/
				BOOL result = NO;
				dvariable *source = new dvariable(dbg, die_cu_child, (vector<location *>)NULL);
				Dwarf_Off off_type_cur = 0;
				Dwarf_Die die_type_cur = 0;
				result = get_die_type(dbg, die_cu_child, &die_type_cur, &off_type_cur);
				if(result == YES && source->var_name!="" && source->loclist.size()>0){
					Dwarf_Half cur_type_tag = 0;
					get_die_tag(die_type_cur, &cur_type_tag);
					switch(cur_type_tag){
					case DW_TAG_base_type:{
						dbase * member = new dbase(*source, die_type_cur, off_type_cur, 0, 0);
						this->global_var_list.push_back(member);
						break;
					}
					case DW_TAG_structure_type:{
						dstruct * member = new dstruct(dbg, *source, die_type_cur, off_type_cur, 0, 0);
						this->global_var_list.push_back(member);
						break;
					}
					case DW_TAG_array_type:{
						darray * member = new darray(dbg, *source, die_type_cur, off_type_cur, 0, 0);
						this->global_var_list.push_back(member);
						break;
					}
					case DW_TAG_pointer_type:{
						dptr * member = new dptr(dbg, *source, die_type_cur, off_type_cur, 0, 0);
						this->global_var_list.push_back(member);
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
				break;
			}
			}

			/*get next child*/
			res = dwarf_siblingof(dbg, die_cu_child, &die_cu_child, &error);
		}
	}
}

void subprogram::print_subprogram(){
	int i;
	cout<<"function:"<<this->name<<endl;
	cout<<"frame_base["<<this->frame_base.size()<<"]:"<<endl;
	for(i = 0; i < this->frame_base.size(); i++){
		cout<<"\t"<<this->frame_base.at(i)->tostring()<<endl;
	}
	for(i = 0; i< this->var_list.size(); i++){
		this->var_list.at(i)->print_me();
		cout<<"*************************"<<endl;
		cout<<endl;
	}
	cout<<"//------------------------------------------------------------------X"<<endl;
}

void program::print_program(){
	int i;
	cout<<"global variable:"<<this->global_var_list.size()<<endl;
	for(i = 0; i < this->global_var_list.size(); i++){
		this->global_var_list.at(i)->print_me();
	}
	cout<<"//------------------------------------------------------------------X"<<endl;
	cout<<"function:"<<this->func_list.size()<<endl;
	for(i = 0; i < this->func_list.size(); i++){
		this->func_list.at(i)->print_subprogram();
	}


}
