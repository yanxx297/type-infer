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

//Functions for reading dbg info of libc
bool libcdbg_read_cu(Dwarf_Debug dbg, string funcname, Dwarf_Die *ret){

	Dwarf_Unsigned cu_header_length = 0;
	Dwarf_Half version_stamp = 0;
	Dwarf_Unsigned abbrev_offset = 0;
	Dwarf_Half address_size = 0;
	Dwarf_Unsigned next_cu_header = 0;
	Dwarf_Error error = 0;
	bool result = false;
	int cu_number = 0;

	for (;; ++cu_number) {
		Dwarf_Die no_die = 0;
		Dwarf_Die cu_die = 0;
		int res = DW_DLV_ERROR;
		res = dwarf_next_cu_header(dbg, &cu_header_length, &version_stamp, &abbrev_offset, &address_size, &next_cu_header, &error);
		if (res == DW_DLV_ERROR) {
			char msg[256];
			sprintf(msg, "Error in libcdbg_read_cu at %d\n", cu_number);
			perror(msg);//TODO:__stack_chk_fail and free fail at there in factor:
			//exit(1);
			return false;
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
		//dwarf_dealloc(dbg, cu_die, DW_DLA_DIE);
		if(result == true){
			break;
		}
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
				dwarf_dealloc(dbg, child, DW_DLA_DIE);
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
				//Dealloc previous DIE
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
		result = get_die_name(dbg, die, name);
		if(result == false){
//			string msg = funcname+":subprogram doesn't have name?";
//			perror(msg.c_str());
			return false;
		}
		//cout<<"die name:"<<name<<endl;
		if(name == funcname
				|| name == "__"+funcname
				|| name == "_"+funcname
				|| name == "__new_"+funcname
				|| name == "_IO_"+funcname
				|| name == "_IO_new_"+funcname
				|| name == "__libc_"+funcname){
			*ret = die;
			cout<<name<<"<=>"<<funcname<<endl;
			return true;
		}
	}

	return false;
}
