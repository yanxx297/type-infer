#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <errno.h>
#include <string>
#include <stdbool.h>

#include "asm_program.h"
#include "disasm-pp.h"
extern "C"
{
#include "libvex.h"
}
#include "irtoir.h"

#include "dwarf.h"
#include "libdwarf.h"

#include <iostream>
#include <vector>

#include "type_common.h"
#include "tmp_s.h"
#include "location.h"
#include "dvar.h"
#include "vine_api.h"
#include "type_dwarf_util.h"
#include "debug_info.h"


static vector<var_info> var_list;
vector<subprog> debug_info;
struct subprog global;

using namespace std;

void test_dvar(Dwarf_Debug dbg){
	program * prog = new program(dbg);
	prog->print_program();
	exit(0);
}


//-----------------------------------------------------------------------------------------------X
/*read CU list one by one*/
static void read_cu_list(Dwarf_Debug dbg) {
	Dwarf_Unsigned cu_header_length = 0;
	Dwarf_Half version_stamp = 0;
	Dwarf_Unsigned abbrev_offset = 0;
	Dwarf_Half address_size = 0;
	Dwarf_Unsigned next_cu_header = 0;
	Dwarf_Error error;
	int cu_number = 0;
	global.subprog_name = "global";
	debug_info.push_back(global);

	for (;; ++cu_number) {
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
			return;
		}
		/* The CU will have a single sibling, a cu_die. */
		res = dwarf_siblingof(dbg, no_die, &cu_die, &error);
		if (res == DW_DLV_ERROR) {
			printf("Error in dwarf_siblingof on CU die \n");
			exit(1);
		}
		if (res == DW_DLV_NO_ENTRY) {
			/* Impossible case. */
			printf("no entry! in dwarf_siblingof on CU die \n");
			exit(1);
		}
		get_die_and_siblings(dbg, cu_die, 0);
		dwarf_dealloc(dbg, cu_die, DW_DLA_DIE);
	}
}

static void get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die, int in_level) {
	int res = DW_DLV_ERROR;
	//int flag = 0;//count error in finding sibling & child
	Dwarf_Die cur_die = in_die;
	Dwarf_Die child = 0;
	Dwarf_Error error;

	print_die_data(dbg, in_die, in_level);

	for (;;) {
		Dwarf_Die sib_die = 0;
		res = dwarf_child(cur_die, &child, &error);
		if (res == DW_DLV_ERROR) {
			printf("Error in dwarf_child , level %d \n", in_level);
			exit(1);
		}
		if (res == DW_DLV_NO_ENTRY) {
			/* Done at this level. */
			printf("No child in this level\n");
			//flag ++;
			//break;
		}
		if (res == DW_DLV_OK) {
			get_die_and_siblings(dbg, child, in_level + 1);
		}

		/* res == DW_DLV_NO_ENTRY */
		res = dwarf_siblingof(dbg, cur_die, &sib_die, &error);
		if (res == DW_DLV_ERROR) {
			printf("Error in dwarf_siblingof , level %d \n", in_level);
			exit(1);
		}
		if (res == DW_DLV_NO_ENTRY) {
			/* Done at this level. */
			printf("No sibling in this level\n");
			//flag ++;
			//if(flag == 2){
				break;
			//}
		}
		/* res == DW_DLV_OK */
		if (cur_die != in_die) {
			dwarf_dealloc(dbg, cur_die, DW_DLA_DIE);
		}
		cur_die = sib_die;
		print_die_data(dbg, cur_die, in_level);
	}
	return;
}

static void handle_var_die(struct subprog &curr_sub, Dwarf_Debug dbg, Dwarf_Die print_me, int level) {
	int res;
	Dwarf_Error error = 0;
	Dwarf_Half tag = 0;
	Dwarf_Die my_type;
	Dwarf_Off offset_type;
	my_type = get_type(dbg, print_me, &offset_type);
	res = dwarf_tag(my_type, &tag, &error);
	bool result = false;
	if (res != DW_DLV_OK) {
		perror("No tag for var DIE");
		exit(1);
	}
	switch (tag) {
	case DW_TAG_base_type:
	case DW_TAG_pointer_type: {
		struct var_info *curr_var;
		result = get_var(dbg, print_me, level + 1, curr_var);
		if (result == true) {
			printf("push %s\n",curr_var->var_name.c_str());
			curr_sub.variable.push_back(curr_var);
		}
		break;
	}
	case DW_TAG_array_type: {
		break;
	}
	case DW_TAG_structure_type: {
		/*structure*/
		/*get_var one by one*/
		struct var_info *curr_var;
		result = get_var(dbg, print_me, level, curr_var);
		if (result == true) {
			Dwarf_Unsigned tmp_loc;
			LOCTYPE tmp_loctype;
			tmp_loctype = curr_var->loc_type;
			if (tmp_loctype == OFFSET) {
				tmp_loc = curr_var->var_offset.offset;
			} else if (tmp_loctype == ADDRESS) {
				tmp_loc = curr_var->var_addr;
			}
			Dwarf_Die cur_mem, next_mem;
			res = dwarf_child(my_type, &next_mem, &error);
			if (res != DW_DLV_OK) {
				printf("Error in getting a child die of array-type\n");
				exit(1);
			}
			while (res == DW_DLV_OK) {
				char *sub_name = 0;
				res = dwarf_diename(print_me, &sub_name, &error);
				if (res != DW_DLV_OK) {
					perror("No name for structure");
					exit(1);
				}
				result = get_var(dbg, next_mem, level + 1, curr_var);
				if (result == true) {
					curr_var->loc_type = tmp_loctype;
					if (tmp_loctype == OFFSET) {
						curr_var->var_offset.offset = tmp_loc;
						tmp_loc += curr_var->var_length;
					} else if (tmp_loctype == ADDRESS) {
						curr_var->var_addr = tmp_loc;
						tmp_loc += curr_var->var_length;
					}
					string name_str = std::string(sub_name);
					curr_var->var_name = name_str + "." + curr_var->var_name;
					curr_sub.variable.push_back(curr_var);
					cur_mem = next_mem;
					res = dwarf_siblingof(dbg, cur_mem, &next_mem, &error);
				}
			}

			break;
		}

	}
	default:
		break;
	}

}

static void handle_lexical_block(struct subprog &curr_sub, Dwarf_Debug dbg, Dwarf_Die lex_die, int level) {
	printf("Find lex\n");

	int res;
	Dwarf_Half tag;
	Dwarf_Die child, child_type, sibling, sibling_type;
	Dwarf_Error error;

//	Handle first child
	res = dwarf_child(lex_die, &child, &error);
	if (res != DW_DLV_OK) {
		perror("lexical has no child");
		exit(1);
	}
	res = dwarf_tag(child, &tag, &error);
	if (res != DW_DLV_OK) {
		perror("lexical has no tag");
		exit(1);
	}
	switch (tag) {
	case DW_TAG_variable:
	case DW_TAG_formal_parameter:
	case DW_TAG_member:{
		handle_var_die(curr_sub, dbg, child, level);
		break;
	}
	case DW_TAG_lexical_block: {
		handle_lexical_block(curr_sub, dbg, child, level + 1);
		break;
	}
	default:
		break;
	}

//    Handle other children (siblings of first child)
	res = dwarf_siblingof(dbg, child, &sibling, &error);
	while (res == DW_DLV_OK) {
		int res_in;
		res_in = dwarf_tag(sibling, &tag, &error);
		if (res_in != DW_DLV_OK) {
			perror("lexical's child has no sibling");
			exit(1);
		}
		switch (tag) {
		case DW_TAG_variable:
		case DW_TAG_formal_parameter:
		case DW_TAG_member:{
			handle_var_die(curr_sub, dbg, sibling, level);
			break;
		}
		case DW_TAG_lexical_block: {
			handle_lexical_block(curr_sub, dbg, sibling, level + 1);
			break;
		}
		default:
			break;
		}

		child = sibling;
		res = dwarf_siblingof(dbg, child, &sibling, &error);
	}
}

void set_location(Dwarf_Die var, struct var_info *&curr_var){
	Dwarf_Locdesc *llbuf;
	Dwarf_Loc *locp;
	int i, j;
	unsigned int entindx;
	Dwarf_Attribute attr;
	Dwarf_Signed count;
	Dwarf_Error error = 0;
	Dwarf_Half tag = 0;
	int res;

	res = dwarf_tag(var, &tag, &error);
	if (res != DW_DLV_OK) {
		perror("var has no tag");
		exit(1);
	}

	res = dwarf_attr(var, DW_AT_location, &attr, &error);
	if (res != DW_DLV_OK) {
		string name = set_name(var);
		perror("var has no attr");
		printf("var name: %s\n",name.c_str());
		exit(1);
	}

	llbuf = 0;
	res = dwarf_loclist(attr, &llbuf, &count, &error);
	if (res != DW_DLV_OK) {
		perror("var has no loclist");
		exit(1);
	}
	for (j = 0; j < count; ++j) {
		unsigned int ents = llbuf[j].ld_cents;

		locp = llbuf[j].ld_s;
		for (entindx = 0; entindx < ents; entindx++) {
			Dwarf_Loc *llocp;

			llocp = locp + entindx;
			if (tag == DW_TAG_formal_parameter) {
				if (llocp->lr_atom == DW_OP_fbreg) {
					curr_var->loc_type = OFFSET;
					curr_var->var_offset.offset = llocp->lr_number + 8;
					curr_var->var_offset.reg_name = DW_OP_breg5;
				}
			} else if (tag == DW_TAG_variable) {
				if (llocp->lr_atom == DW_OP_fbreg) {
					curr_var->loc_type = OFFSET;
					curr_var->var_offset.offset = llocp->lr_number + 8;
					curr_var->var_offset.reg_name = DW_OP_breg5;
				} else if (llocp->lr_atom >= DW_OP_breg0
						&& llocp->lr_atom <= DW_OP_breg31) {
					curr_var->loc_type = OFFSET;
					curr_var->var_offset.offset = llocp->lr_number;
					curr_var->var_offset.reg_name = llocp->lr_atom;
				} else if (llocp->lr_atom == DW_OP_addr) {
					curr_var->loc_type = ADDRESS;
					curr_var->var_addr = llocp->lr_number;
				}
			} else {

			}
		}
	}
}

//given DIE -> its type -> its size
void set_length(Dwarf_Die die, struct var_info *&curr_var, Dwarf_Debug dbg){
	int res;
	Dwarf_Half type_tag;
	Dwarf_Attribute attr;
	Dwarf_Error error = 0;
	Dwarf_Off offset_type;
	Dwarf_Unsigned byte_size;
	Dwarf_Die typeDie = get_type(dbg, die, &offset_type);
	res = dwarf_tag(typeDie, &type_tag, &error);
	if (type_tag == DW_TAG_base_type || type_tag == DW_TAG_pointer_type) {
		/*Get length*/
		res = dwarf_attr(typeDie, DW_AT_byte_size, &attr, &error);
		if (res == DW_DLV_OK) {
			res = dwarf_formudata(attr, &byte_size, &error);
			curr_var->var_length = byte_size;
		}else{
			perror("var has no size attr");
			exit(1);
		}
	}else{
		curr_var->var_length = 0;
	}
}

//die -> die's DW_AT_encoding ->s or u
Dwarf_Unsigned set_su(Dwarf_Die die){
	int res;
	Dwarf_Unsigned s_u;
	Dwarf_Attribute attr;
	Dwarf_Error error;
	res = dwarf_attr(die, DW_AT_encoding, &attr, &error);
	if (res != DW_DLV_OK) {
		perror("var has no s/u attr");
		exit(1);
	}
	res = dwarf_formudata(attr, &s_u, &error);
	if (res != DW_DLV_OK) {
		perror("fail to get the value of s/u attr");
		exit(1);
	}

	return s_u;
}

//Set the offset inside of a structure
//var is the DIE of a structure member
int set_offset(Dwarf_Die var){
	Dwarf_Locdesc *llbuf;
	Dwarf_Loc *locp;
	int i, j;
	unsigned int entindx;
	Dwarf_Attribute attr;
	Dwarf_Signed count;
	Dwarf_Error error = 0;
	Dwarf_Half tag = 0;
	int res;
	int offset = -1;

	res = dwarf_attr(var, DW_AT_data_member_location, &attr, &error);
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
			}
		}
	}

	return offset;

}

//return the name of given DIE
string set_name(Dwarf_Die die){
	char *name = 0;
	string ret;
	Dwarf_Error error = 0;
	int res;

	res = dwarf_diename(die, &name, &error);
	if (res == DW_DLV_ERROR) {
		perror("Fail to get var name");
		exit(1);
	}

	ret = std::string(name);
	return ret;
}

//Special handler for pointer to a structure array
void get_struct_ptr(Dwarf_Debug dbg, Dwarf_Die var, Dwarf_Off type_offset, Dwarf_Die stru, Dwarf_Die member, struct var_info *&ret){
	//printf("run get_struct_ptr, %p\n",var);
	struct var_info *curr_var = new struct var_info();
	string name;
	string sub_name;
	int localname = 0;
	Dwarf_Error error = 0;
	int res;

	/*get name attr*/
	//string tmp_name;
//	res = dwarf_diename(var, &name, &error);
//	if (res == DW_DLV_ERROR) {
//		exit(1);
//	}
//		if (res == DW_DLV_NO_ENTRY) {
//		name = "<no DW_AT_name attr>";
//		localname = 1;
//	}

	//strcat(name, ".");
	name = set_name(var);
	//printf("name = %s\n",name.c_str());
	//curr_var->var_name = tmp_name;

//	res = dwarf_diename(member, &sub_name, &error);
//	if (res == DW_DLV_ERROR) {
//		exit(1);
//	}
//
//	tmp_name = std::string(sub_name);

	sub_name = set_name(member);
	curr_var->var_name = name + "." + sub_name;


	/*get location*/
	set_location(var, curr_var);

	/*get length*/
	set_length(member, curr_var, dbg);

	curr_var->array_pos = -1;
	curr_var->su_type = 0;

	/*Set pointed_info*/
	curr_var->pointed_info.offset = type_offset;

	Dwarf_Die member_type;
	Dwarf_Off member_type_offset;
	member_type = get_type(dbg, member, &member_type_offset);
	curr_var->pointed_info.su_type = set_su(member_type);

	curr_var->pointed_info.offset_strucr = set_offset(member);

	curr_var->pointed_info.addr_set = false;

	ret = curr_var;

}

static void print_die_data(Dwarf_Debug dbg, Dwarf_Die print_me, int level) {
	char *name = 0;
	Dwarf_Error error = 0;
	Dwarf_Half tag = 0;
	Dwarf_Attribute attr;
	Dwarf_Off offset_type;
	struct var_info *curr_var;
	int localname = 0;
	int i, j, k;
	int res;
	bool result = false;

	/*get tag attr*/
	res = dwarf_tag(print_me, &tag, &error);
	if (res != DW_DLV_OK) {
		printf("Error in dwarf_tag , level %d \n", level);
		exit(1);
	}

	printf("tag:%x\n",tag);

	/*only process on sub_program*/
	if (tag == DW_TAG_subprogram && level == 1) {
		struct subprog curr_sub;

		/*get name attr*/
//		res = dwarf_diename(print_me, &name, &error);
//		if (res == DW_DLV_ERROR) {
//			printf("Error in dwarf_diename , level %d \n", level);
//			exit(1);
//		}
		curr_sub.subprog_name = set_name(print_me);
		printf("find subprogram %s\n",curr_sub.subprog_name.c_str());

		Dwarf_Die cur_die, next_die, type_die;
		res = dwarf_child(print_me, &next_die, &error);

		char *sub_name = 0;
		Dwarf_Half tag_next;
		while (res == DW_DLV_OK) {
			res = dwarf_tag(next_die, &tag_next, &error);
			if (res != DW_DLV_OK) {
				perror("Fail to get TAG of next DIE");
				exit(1);
			}
			switch (tag_next) {
			case DW_TAG_variable:
			case DW_TAG_formal_parameter:
			case DW_TAG_member: {
				res = dwarf_diename(next_die, &sub_name, &error);
				type_die = get_type(dbg, next_die, &offset_type);
				res = dwarf_tag(type_die, &tag, &error);
				if (res != DW_DLV_OK) {
					perror("Fail to get tag of type DIE");
					exit(1);
				}

				if (tag == DW_TAG_base_type) {
					result = get_var(dbg, next_die, level + 1, curr_var);
					if (result == true) {
						curr_sub.variable.push_back(curr_var);
					}

				} else if(tag == DW_TAG_pointer_type){
					Dwarf_Off ptr_off;
					Dwarf_Half ptr_tag;
					Dwarf_Die ptr_type = get_type(dbg, type_die, &ptr_off);
					res = dwarf_tag(ptr_type, &ptr_tag, &error);
					if(res != DW_DLV_OK){
						perror("Fail to get tag of ptr_type");
						exit(1);
					}
					//printf("type: %x\n", ptr_tag);
					if(ptr_tag == DW_TAG_structure_type){
						//Handle this situation separately
						//printf("Find a DW_TAG_structure_type\n");
						Dwarf_Die member_die;
						res = dwarf_child(ptr_type, &member_die, &error);
						if (res != DW_DLV_OK) {
							perror("Fail to get child of ptr_type");
							exit(1);
						}
						while(res == DW_DLV_OK){
							Dwarf_Half member_tag;
							res = dwarf_tag(member_die, &member_tag, &error);
							if (res != DW_DLV_OK) {
								perror("Fail to get tag of member_die");
								exit(1);
							}
							if(member_tag == DW_TAG_member){
								//Add debug info
								//printf("Add debug info of a struct member\n");
								get_struct_ptr(dbg, next_die, ptr_off, ptr_type, member_die, curr_var);
								curr_sub.variable.push_back(curr_var);
							}

							res = dwarf_siblingof(dbg, member_die, &member_die, &error);
						}
					}else{
						result = get_var(dbg, next_die, level + 1, curr_var);
						if (result == true) {
							curr_sub.variable.push_back(curr_var);
						}
					}
				}else if (tag == DW_TAG_array_type) {
					/*Array*/
					Dwarf_Die subrange;
					res = dwarf_child(type_die, &subrange, &error);
					if (res != DW_DLV_OK) {
						printf("Cannot get DIE of subrange\n");
						exit(1);
					}
					Dwarf_Half sub_tag = 0;
					res = dwarf_tag(subrange, &sub_tag, &error);
					if (sub_tag != DW_TAG_subrange_type) {
						printf("Error: Invalid tag %d\n", sub_tag);
					} else {
						printf("Get tag DW_TAG_subrange_type\n");

						Dwarf_Attribute attr;
						Dwarf_Unsigned array_size = 0;
						res = dwarf_attr(subrange, DW_AT_upper_bound, &attr,
								&error);
						if (res == DW_DLV_OK) {
							res = dwarf_formudata(attr, &array_size, &error);
							printf("array_size:%d\n", array_size);
							Dwarf_Die array_type = get_type(dbg, type_die, &offset_type);
							Dwarf_Half array_type_tag = 0;
							res = dwarf_tag(array_type, &array_type_tag,
									&error);
							printf("array_type_tag:%d\n", array_type_tag);
							if (array_type_tag == DW_TAG_base_type) {
								for (i = 0; i < array_size; i++) {
									curr_var = get_array_member(dbg, next_die,
											type_die, i, level);
									printf("var_len: %d\n",
											curr_var->var_length);
									if (curr_var->var_length != 0) {
										curr_sub.variable.push_back(curr_var);
									}
								}
							} else if (array_type_tag == DW_TAG_structure_type) {
								/*Handle struct array*/
								for (i = 0; i < array_size; i++) {
									Dwarf_Unsigned tmp_loc = 0;
									Dwarf_Die cur_mem, next_mem;
									while (res == DW_DLV_OK) {
										curr_var = get_array_member(dbg,
												next_die, type_die, i, level);
										//curr_var->loc_type = tmp_loctype;

										if (curr_var->loc_type == OFFSET) {
											curr_var->var_offset.offset =
													tmp_loc;
											tmp_loc += curr_var->var_length;
										} else if (curr_var->loc_type
												== ADDRESS) {
											curr_var->var_addr = tmp_loc;
											tmp_loc += curr_var->var_length;
										}
										string name_str = std::string(sub_name);
										curr_var->var_name = name_str + "."
												+ curr_var->var_name;
										//cout<<curr_var.var_name<<endl;
										curr_sub.variable.push_back(curr_var);
										cur_mem = next_mem;
										res = dwarf_siblingof(dbg, cur_mem,
												&next_mem, &error);
									}

								}
							}
						}
					}
				} else if (tag == DW_TAG_structure_type) {
					/*structure*/
					/*get_var one by one*/
					result = get_var(dbg, next_die, level, curr_var);
					if (result == true) {
						Dwarf_Unsigned tmp_loc;
						LOCTYPE tmp_loctype;
						tmp_loctype = curr_var->loc_type;
						if (tmp_loctype == OFFSET) {
							tmp_loc = curr_var->var_offset.offset;
						} else if (tmp_loctype == ADDRESS) {
							tmp_loc = curr_var->var_addr;
						}
						Dwarf_Die cur_mem, next_mem;
						res = dwarf_child(type_die, &next_mem, &error);
						if (res != DW_DLV_OK) {
							printf(
									"Error in getting a child die of array-type\n");
							exit(1);
						}
						while (res == DW_DLV_OK) {
							result = get_var(dbg, next_mem, level + 1, curr_var);
							if(result == true){
								curr_var->loc_type = tmp_loctype;
								if (tmp_loctype == OFFSET) {
									curr_var->var_offset.offset = tmp_loc;
									tmp_loc += curr_var->var_length;
								} else if (tmp_loctype == ADDRESS) {
									curr_var->var_addr = tmp_loc;
									tmp_loc += curr_var->var_length;
								}
								string name_str = std::string(sub_name);
								curr_var->var_name = name_str + "."
										+ curr_var->var_name;
								curr_sub.variable.push_back(curr_var);
								cur_mem = next_mem;
								res = dwarf_siblingof(dbg, cur_mem, &next_mem,&error);
							}
						}
					}

				}
				break;
			}
			case DW_TAG_lexical_block: {
				handle_lexical_block(curr_sub, dbg, next_die, level + 1);
				break;
			}
			default:
				break;
			};

			cur_die = next_die;
			res = dwarf_siblingof(dbg, cur_die, &next_die, &error);

		}
		printf("push %s into debug_info\n",curr_sub.subprog_name.c_str());
		debug_info.push_back(curr_sub);
	} else if (tag == DW_TAG_variable && level == 1) {
		/*global variable*/
		result = get_var(dbg, print_me, level + 1, curr_var);
		if (result == true) {
			debug_info.at(0).variable.push_back(curr_var);
		}
	}

	if (!localname) {
		dwarf_dealloc(dbg, name, DW_DLA_STRING);
	}
}

static struct var_info *get_array_member(Dwarf_Debug dbg, Dwarf_Die print_me,
		Dwarf_Die array_info, int pos, int level) {
	struct var_info *curr_var = new struct var_info();
	char *name = 0;
	Dwarf_Error error = 0;
	Dwarf_Loc *locp;
	unsigned int entindx;
	Dwarf_Half tag = 0;
	Dwarf_Attribute attr;
	Dwarf_Signed attrcount;
	Dwarf_Locdesc *llbuf;
	Dwarf_Signed count;
	Dwarf_Unsigned byte_size;
	Dwarf_Unsigned s_u;
	const char *opname = 0;
	const char *tagname = 0;
	int localname = 0;
	int i, j, k;
	int res;

	curr_var->array_pos = pos;

	/*get tag attr*/
	res = dwarf_tag(print_me, &tag, &error);
	if (res != DW_DLV_OK) {
		printf("Error in dwarf_tag , level %d \n", level);
		exit(1);
	}

	if (tag == DW_TAG_variable) {

		/*get name attr*/
//		res = dwarf_diename(print_me, &name, &error);
//		if (res == DW_DLV_ERROR) {
//			printf("Error in dwarf_diename , level %d \n", level);
//			exit(1);
//		}
//		if (res == DW_DLV_NO_ENTRY) {
//			name = "<no DW_AT_name attr>";
//			localname = 1;
//		}
		curr_var->var_name = set_name(print_me);

		/*get tagname attr*/
		res = dwarf_get_TAG_name(tag, &tagname);
		if (res != DW_DLV_OK) {
			printf("Error in dwarf_get_TAG_name , level %d \n", level);
			exit(1);
		}

		/*get loclist attr*/
		set_location(print_me, curr_var);
//		res = dwarf_attr(print_me, DW_AT_location, &attr, &error);
//		if (res == DW_DLV_OK) {
//			llbuf = 0;
//			int res = dwarf_loclist(attr, &llbuf, &count, &error);
//			if (res != DW_DLV_OK) {
//				printf("Error in dwarf_loclist , level %d \n", level);
//				exit(1);
//			}
//			for (j = 0; j < count; ++j) {
//				unsigned int ents = llbuf[j].ld_cents;
//
//				locp = llbuf[j].ld_s;
//				for (entindx = 0; entindx < ents; entindx++) {
//					Dwarf_Loc *llocp;
//
//					llocp = locp + entindx;
//					if (tag == DW_TAG_formal_parameter) {
//						if (llocp->lr_atom == DW_OP_fbreg) {
//							curr_var->loc_type = OFFSET;
//							curr_var->var_offset.offset = llocp->lr_number + 8;
//							curr_var->var_offset.reg_name = DW_OP_breg5;
//						}
//					} else if (tag == DW_TAG_variable) {
//						if (llocp->lr_atom == DW_OP_fbreg) {
//							curr_var->loc_type = OFFSET;
//							curr_var->var_offset.offset = llocp->lr_number + 8;
//							curr_var->var_offset.reg_name = DW_OP_breg5;
//						} else if (llocp->lr_atom >= DW_OP_breg0
//								&& llocp->lr_atom <= DW_OP_breg31) {
//							curr_var->loc_type = OFFSET;
//							curr_var->var_offset.offset = llocp->lr_number;
//							curr_var->var_offset.reg_name = llocp->lr_atom;
//						} else if (llocp->lr_atom == DW_OP_addr) {
//							curr_var->loc_type = ADDRESS;
//							curr_var->var_addr = llocp->lr_number;
//							//dwarf_get_OP_name(llocp->lr_atom, &opname);
//						}
//					} else {
//
//					}
//				}
//			}
//		}

		/*get size*/
		Dwarf_Off offset;
		/*attr -> offset*/
		res = dwarf_attr(array_info, DW_AT_type, &attr, &error);
		if (res == DW_DLV_OK) {
			res = dwarf_global_formref(attr, &offset, &error);
			if (res != DW_DLV_OK) {
				perror("fail to get global formeref of type attr (array)");
				exit(1);
			}
			Dwarf_Die typeDie = 0;

			/*offset -> DIE*/
			res = dwarf_offdie_b(dbg, offset, 1, &typeDie, &error);/*IS info.*/
			if (res != DW_DLV_OK) {
				perror("fail to get offset in (array)");
				exit(1);
			}

			res = dwarf_tag(typeDie, &tag, &error);
			//curr_var->type_die = typeDie;

			if (tag == DW_TAG_base_type || tag == DW_TAG_pointer_type) {
				/*Get length*/
				res = dwarf_attr(typeDie, DW_AT_byte_size, &attr, &error);
				if (res == DW_DLV_OK) {
					res = dwarf_formudata(attr, &byte_size, &error);
					curr_var->var_length = byte_size;
				}

				if (tag == DW_TAG_base_type) {
					/*Get signed or unsigned*/
					res = dwarf_attr(typeDie, DW_AT_encoding, &attr, &error);
					if (res == DW_DLV_OK) {
						res = dwarf_formudata(attr, &s_u, &error);
						curr_var->su_type = s_u;
					}
				} else {
					/*Pointer*/
					/////////!!!!!!!!!!!!!!!!!!!!!!!
					/////Not handled yet!!!!!!!!!!
					curr_var->su_type = 0;
				}
			} else if (tag == DW_TAG_array_type) {
				//handle each member of an array
			}

		}

		/*Add extra offset in array*/
		if (curr_var->loc_type == ADDRESS) {
			curr_var->var_addr += (pos * (curr_var->var_length));
		} else if (curr_var->loc_type == OFFSET) {
			curr_var->var_offset.offset += (pos * (curr_var->var_length));
		}

	} else {
		curr_var->var_length = 0;
	}

	return curr_var;

}

static bool get_var(Dwarf_Debug dbg, Dwarf_Die print_me, int level, struct var_info *&ret) {
	//printf("get var\n");
	bool result = false;
	struct var_info *curr_var = new struct var_info();
	char *name = 0;
	Dwarf_Error error = 0;
	Dwarf_Loc *locp;
	unsigned int entindx;
	Dwarf_Half tag = 0;
	Dwarf_Attribute attr;
	Dwarf_Signed attrcount;
	Dwarf_Locdesc *llbuf;
	Dwarf_Signed count;
	Dwarf_Unsigned byte_size;
	Dwarf_Unsigned s_u;
	const char *opname = 0;
	const char *tagname = 0;
	int localname = 0;
	int i, j, k;
	int res;
	Dwarf_Off offset_type;

	curr_var->array_pos = -1;

	/*get tag attr*/
	res = dwarf_tag(print_me, &tag, &error);
	if (res != DW_DLV_OK) {
		printf("Error in dwarf_tag , level %d \n", level);
		exit(1);
	}

	if (tag == DW_TAG_variable || tag == DW_TAG_formal_parameter || tag == DW_TAG_member) {

		/*get name attr*/
//		res = dwarf_diename(print_me, &name, &error);
//		if (res == DW_DLV_ERROR) {
//			printf("Error in dwarf_diename , level %d \n", level);
//			exit(1);
//		}
//		if (res == DW_DLV_NO_ENTRY) {
//			name = "<no DW_AT_name attr>";
//			localname = 1;
//		}
		curr_var->var_name = set_name(print_me);

		/*get tagname attr*/
		res = dwarf_get_TAG_name(tag, &tagname);
		if (res != DW_DLV_OK) {
			printf("Error in dwarf_get_TAG_name , level %d \n", level);
			exit(1);
		}

		/*get loclist attr*/
		set_location(print_me, curr_var);

		/*get size*/
		set_length(print_me, curr_var, dbg);


		Dwarf_Die typeDie = get_type(dbg, print_me, &offset_type);
		res = dwarf_tag(typeDie, &tag, &error);
		if (tag == DW_TAG_base_type || tag == DW_TAG_pointer_type) {

			if (tag == DW_TAG_base_type) {
				/*Get signed or unsigned*/
//				res = dwarf_attr(typeDie, DW_AT_encoding, &attr, &error);
//				if (res == DW_DLV_OK) {
//					res = dwarf_formudata(attr, &s_u, &error);
//					curr_var->su_type = s_u;
//				}
				curr_var->su_type = set_su(typeDie);

				ret = curr_var;
				result = true;
			} else {
				/*Pointer*/
				//char *name = 0;

				Dwarf_Die pointer_type = get_type(dbg, typeDie, &offset_type);

				/*check whether its still a pointer*/
				Dwarf_Half ptr_tag;
				res = dwarf_tag(pointer_type, &ptr_tag, &error);
				if(ptr_tag == DW_TAG_base_type){
					/*Get signed or unsigned*/
//					res = dwarf_attr(pointer_type, DW_AT_encoding, &attr, &error);
//					if (res != DW_DLV_OK) {
//						exit(1);
//					}
//					res = dwarf_formudata(attr, &s_u, &error);
//					if (res != DW_DLV_OK) {
//						exit(1);
//					}
					s_u = set_su(pointer_type);
				}else if(ptr_tag == DW_TAG_pointer_type){
					s_u = 0;
				}else if(ptr_tag == DW_TAG_structure_type){
					/*Do nothing*/
					/*handle this condition separately*/
					result = false;
					return result;
				}else{}

				//curr_var->type_die = pointer_type;
				curr_var->su_type = 0;
				curr_var->pointed_info.offset = offset_type;
				curr_var->pointed_info.offset_strucr = -1;
				curr_var->pointed_info.su_type = s_u;
				curr_var->pointed_info.addr_set = false;

				ret = curr_var;
				result = true;
			}
		}

	} else {
		result = false;
		curr_var->var_length = 0;
	}

	return result;
}

static Dwarf_Die get_type(Dwarf_Debug dbg, Dwarf_Die curr_die, Dwarf_Off *type_offset) {
	/*return the type die of curr_die*/
	int res;
	Dwarf_Attribute attr;
	Dwarf_Off offset;
	Dwarf_Half tag;
	Dwarf_Error error;
	Dwarf_Die typeDie = 0;
	char *name = 0;
	Dwarf_Off offset_type;

	res = dwarf_diename(curr_die, &name, &error);

	res = dwarf_attr(curr_die, DW_AT_type, &attr, &error);
	if (res == DW_DLV_OK) {
		res = dwarf_global_formref(attr, &offset, &error);
		if (res != DW_DLV_OK) {
			perror("fail to get global formref (get_type)");
			exit(1);
		}


		/*offset -> DIE*/
		res = dwarf_offdie_b(dbg, offset, 1, &typeDie, &error);/*IS info.*/
		if (res != DW_DLV_OK) {
			perror("fail to get dwarf offdie b (get_type)");
			exit(1);
		}

		/*check whether the type is a typedef*/
		Dwarf_Half tag;
		res = dwarf_tag(typeDie, &tag, &error);
		if(res != DW_DLV_OK){
			perror("fail to get tag of type DIE (get_type)");
			exit(1);
		}
		//printf("tag:%d\n",tag);
		if(tag == DW_TAG_typedef){
			//printf("DW_TAG_typedef\n");
			typeDie = get_type(dbg, typeDie, &offset_type);
		}
	} else {
		//res = dwarf_diename(curr_die, &name, &error);
		printf("%s cannot get type\n", name);
	}

	//printf("%s:%d\n",name, offset);
	*type_offset = offset;
	return typeDie;

}

//static void print_debug_info(vector<subprog> dbg) {
//	unsigned int subprog_num, var_num;
//	Dwarf_Error error = 0;
//	int i, j, res;
//	subprog_num = dbg.size();
//	printf(
//			"***********************start_printing_debug_info***********************\n");
//	for (i = 0; i < subprog_num; i++) {
//		cout << "function:" << dbg.at(i).subprog_name << endl;
//		var_num = dbg.at(i).variable.size();
//		for (j = 0; j < var_num; j++) {
//			cout << "var_name:" << dbg.at(i).variable.at(j)->var_name;
//			if (dbg.at(i).variable.at(j)->array_pos != -1) {
//				printf("[%d]\n", dbg.at(i).variable.at(j)->array_pos);
//			} else {
//				printf("\n");
//			}
//			printf("\tvar_length:%d\n", dbg.at(i).variable.at(j)->var_length);
//			if (dbg.at(i).variable.at(j)->loc_type == OFFSET) {
//				printf("\tvar_location:offset %d\t",
//						dbg.at(i).variable.at(j)->var_offset.offset);
//				switch (dbg.at(i).variable.at(j)->var_offset.reg_name) {
//				case DW_OP_breg4: {
//					printf("from ESP\n");
//					break;
//				}
//				case DW_OP_breg5: {
//					printf("from EBP\n");
//					break;
//				}
//				}
//			} else if (dbg.at(i).variable.at(j)->loc_type == ADDRESS) {
//				printf("\tvar_location:address %x\n",
//						dbg.at(i).variable.at(j)->var_addr);
//			}
//
//			/*Print signed or unsigned */
//			if (dbg.at(i).variable.at(j)->su_type == DW_ATE_unsigned
//					|| dbg.at(i).variable.at(j)->su_type == DW_ATE_unsigned_char) {
//				printf("\tvar_type: Unsigned\n");
//			} else if (dbg.at(i).variable.at(j)->su_type == DW_ATE_signed
//					|| dbg.at(i).variable.at(j)->su_type == DW_ATE_signed_char) {
//				printf("\tvar_type: Signed\n");
//			} else if (dbg.at(i).variable.at(j)->su_type == 0) {
//				printf("\tPointer\n");
//
//				/*Print pointed*/
//				printf("\t\tType offset :%x\n", dbg.at(i).variable.at(j)->pointed_info.offset);
//				printf("\t\struct offset :%d\n", dbg.at(i).variable.at(j)->pointed_info.offset_strucr);
//				if(dbg.at(i).variable.at(j)->pointed_info.su_type == DW_ATE_unsigned
//						|| dbg.at(i).variable.at(j)->pointed_info.su_type == DW_ATE_unsigned_char){
//					printf("\t\t\tvar_type: Unsigned\n");
//				}else if(dbg.at(i).variable.at(j)->pointed_info.su_type == DW_ATE_signed
//						|| dbg.at(i).variable.at(j)->pointed_info.su_type == DW_ATE_signed_char){
//					printf("\t\t\tvar_type: Signed\n");
//				}else if(dbg.at(i).variable.at(j)->pointed_info.su_type == 0){
//					printf("\t\t\tPointer\n");
//				}
//			}
//
//
//
//		}
//	}
//}

//==========================================================================================X
//Functions for reading dbg info of libc

bool libcdbg_read_cu(Dwarf_Debug dbg, string funcname, Dwarf_Die *ret){

	Dwarf_Unsigned cu_header_length = 0;
	Dwarf_Half version_stamp = 0;
	Dwarf_Unsigned abbrev_offset = 0;
	Dwarf_Half address_size = 0;
	Dwarf_Unsigned next_cu_header = 0;
	Dwarf_Error error;
	bool result = false;
	int cu_number = 0;

	for (;; ++cu_number) {
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
			break;
		}
		/* The CU will have a single sibling, a cu_die. */
		res = dwarf_siblingof(dbg, no_die, &cu_die, &error);
		if (res == DW_DLV_ERROR) {
			printf("Error in dwarf_siblingof on CU die \n");
			exit(1);
		}
		if (res == DW_DLV_NO_ENTRY) {
			/* Impossible case. */
			printf("no entry! in dwarf_siblingof on CU die \n");
			exit(1);
		}
		result = get_libcfunc_die(dbg, funcname, cu_die, ret, 0);
		if(result == true){
			break;
		}
		//dwarf_dealloc(dbg, cu_die, DW_DLA_DIE);
	}

	return result;
}

bool get_libcfunc_die(Dwarf_Debug dbg, string funcname, Dwarf_Die in_die, Dwarf_Die *ret, int in_level){
	int res = DW_DLV_ERROR;
	Dwarf_Die cur_die = in_die;
	Dwarf_Die child = 0;
	Dwarf_Error error;
	bool result = false;

	result  = check_funcname(dbg, funcname, in_die, ret, in_level);

	if(result == false){
		for (;;) {
			Dwarf_Die sib_die = 0;
			res = dwarf_child(cur_die, &child, &error);
			if (res == DW_DLV_ERROR) {
				printf("Error in dwarf_child , level %d \n", in_level);
				exit(1);
			}
			if (res == DW_DLV_NO_ENTRY) {
				/* Done at this level. */
				//printf("No child in this level\n");
				//break;
			}
			if (res == DW_DLV_OK) {
				result = get_libcfunc_die(dbg, funcname, child, ret, in_level + 1);
				if(result == true){
					break;
				}
			}

			res = dwarf_siblingof(dbg, cur_die, &sib_die, &error);
			if (res == DW_DLV_ERROR) {
				printf("Error in dwarf_siblingof , level %d \n", in_level);
				exit(1);
			}
			if (res == DW_DLV_NO_ENTRY) {
				/* Done at this level. */
				//printf("No sibling in this level\n");
				break;
			}

			if (cur_die != in_die) {
				dwarf_dealloc(dbg, cur_die, DW_DLA_DIE);
			}
			cur_die = sib_die;
			result = check_funcname(dbg, funcname, cur_die, ret, in_level);
			if(result == true){
				break;
			}
		}
	}

	return result;
}

bool check_funcname(Dwarf_Debug dbg, string funcname, Dwarf_Die die, Dwarf_Die *ret, int level){
	string name;
	Dwarf_Error error = 0;
	Dwarf_Half tag = 0;
	int res;
	bool result = false;

	res = dwarf_tag(die, &tag, &error);
	if (res != DW_DLV_OK) {
		printf("Error in dwarf_tag , level %d \n", level);
		exit(1);
	}

	if (tag == DW_TAG_subprogram && level == 1) {
		result = get_die_name(die, name);
		if(result == false){
//			string msg = funcname+":subprogram doesn't have name?";
//			perror(msg.c_str());
			return false;
		}
		//cout<<"die name:"<<name<<endl;
		if(name == funcname || name == "__"+funcname || name == "_IO_"+funcname || name == "_IO_new_"+funcname){
			*ret = die;
			cout<<name<<"<=>"<<funcname<<endl;
			return true;
		}
	}

	return false;
}
