#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>
#include <utility>
#include <stdbool.h>

/*include libdwarf*/
#include "dwarf.h"
#include "libdwarf.h"

/*include BGL*/
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/breadth_first_search.hpp>

#include <boost/graph/copy.hpp>

#include <boost/graph/incremental_components.hpp>
#include <boost/pending/disjoint_sets.hpp>

#include <boost/graph/boykov_kolmogorov_max_flow.hpp>
#include <boost/graph/push_relabel_max_flow.hpp>

/*include Vine*/
#include "asm_program.h"
#include "disasm-pp.h"
extern "C"
{
#include "libvex.h"
}
#include "irtoir.h"


#include "type_common.h"
#include "location.h"
#include "tmp_s.h"
#include "dvar.h"
#include "vine_api.h"
#include "vertex.h"
#include "infer.h"
#include "type_dwarf_util.h"


#include "ptr_handler.h"


//-1 if not found on current equal
//-2 if should stop
int check_reg_for_offset(Exp *equal, Tmp_s *exp){
	int result = -1;
	switch(equal->exp_type){
	case TEMP:{
		//Stop if find a register with the same name and larger index number than exp
		Temp *reg = (Temp *)equal;
		if(get_reg_position(reg->name) == -1){
			break;
		}
		Tmp_s *reg_s = (Tmp_s *)reg;
		if(reg_s->name == exp->name && reg_s->index > exp->index){
			result = -2;
			return result;
		}
		break;
	}
	case MEM:{
		//return offset
		Mem * memory = (Mem *)equal;
		if(memory->addr->exp_type == BINOP){
			//mem[reg + offset], offset is a constant
			BinOp *address = (BinOp *)memory->addr;
			Temp *reg;
			Tmp_s *reg_s;
			int constant;
			if(address->lhs->exp_type == TEMP && address->rhs->exp_type == CONSTANT){
				reg = (Temp *)address->lhs;
				constant = ((Constant *)address->rhs)->val;
			}else if(address->rhs->exp_type == TEMP && address->lhs->exp_type == CONSTANT){
				reg = (Temp *)address->rhs;
				constant = ((Constant *)address->lhs)->val;
			}else{
				break;
			}

			//printf("constant of %s is %d\n", address->rhs->tostring().c_str(),constant);
			if(get_reg_position(reg->name) == -1){
				break;
			}
			reg_s = (Tmp_s *)reg;
			if(reg_s->index == exp->index){
				result = constant;
				return result;
			}else{
				break;
			}
		}else if(memory->addr->exp_type == TEMP){
			//mem[reg], offset = 0;
			Temp *reg = (Temp *)memory->addr;
			if(get_reg_position(reg->name) == -1){
				break;
			}
			Tmp_s *reg_s = (Tmp_s *)reg;
			if(reg_s->index == exp->index){
				result = 0;
				return result;
			}else{
				break;
			}
		}
		break;
	}
	default:{
		break;
	}
	}

	return result;
}

//check whether ptr is already added into plist
//Note that plist is pointer itself, rather than variables pointed by a pointer (ptarget)
int check_plist(dptr *ptr, vector<pointer_info *> plist){
	int i;
	int res = -1;
	for(i = 0; i< plist.size(); i++){
		if(plist.at(i)->debug_info->cmp_type(ptr) == true){
			res = i;
			break;
		}
	}
	return res;
}

//Check duplicated ptarget
//Check whether the type of <ptr> already exist
//Return position in vector if found
int check_ptr(dvariable * ptr, vector<Pointed *> &ptarget_list){
	int res = -1;
	int i;
	for(i = 0; i < ptarget_list.size(); i++){
		if(ptarget_list.at(i)->cmp_ptr_type(ptr) == true){
			res = i;
			break;
		}
	}

	return res;
}


//look for the most recent mem[] = reg
//return reg's descriptor
int copy_from_reg_lookup(func_vertex_ptr func_block, int block, int stmt, Mem *exp){
	bool result = false;
	int ret = -1;
	int i, j;

	for(i = block; i > 0; i--){
		if(i == block){
			j = stmt;
		}else{
			j = func_block->stmt_block->block_list[i]->blen - 1;
		}
		for(;j>=0; j--){
			if(func_block->stmt_block->block_list[i]->block[j]->stmt_type == MOVE){
				Move *equal = (Move *)func_block->stmt_block->block_list[i]->block[j];
				if(equal->lhs->exp_type == MEM &&
						equal->rhs->exp_type == TEMP){
					//Mem[] = reg
					Exp *addr = ((Mem *)equal->lhs)->addr;

					//addr should be the same address of Mem *exp, if so
					//Look for the descriptor of reg
					bool mem_cmp = compare_mem(exp, (Mem *)equal->lhs);
					if(mem_cmp == true){
						result = search_reg(func_block, (Tmp_s *)equal->rhs);
						if(result == true){
							ret = func_block->reg_list.at(((Tmp_s *)equal->rhs)->index)->my_descriptor;
							return ret;
						}
					}


				}
			}
		}
	}

	return ret;
}

void get_ptr_copy(func_vertex_ptr func_block, Move *exp, int block, int stmt){
	int i, j, k;
	address_t pc = exp->asm_address;
	Tmp_s * reg1 = 0;
	Tmp_s * reg2 = 0;
	int cons = -1;
	if(is_tmps(exp->lhs) == true){
		reg1 = (Tmp_s *)exp->lhs;
		Mem * mem = 0;
		if(exp->rhs->exp_type == BINOP){
			BinOp * binop = (BinOp *)exp->rhs;
			if(is_tmps(binop->lhs) == true && binop->rhs->exp_type == MEM){
				/*reg1 = reg0 + mem[reg2 (+ cons)]*/
				mem = (Mem *)binop->rhs;
			}else if(is_tmps(binop->rhs) == true && binop->lhs->exp_type == MEM){
				/*reg1 = mem[reg2 (+ cons)] + reg0*/
				mem = (Mem *)binop->lhs;
			}else{
				return;
			}
		}else if(exp->rhs->exp_type == MEM){
			/* reg1 = mem[reg2 (+ cons)]*/
			mem = (Mem *)exp->rhs;
		}else{
			return;
		}


		if(mem->addr->exp_type == BINOP ){
			BinOp *addr = (BinOp *)mem->addr;
			if(is_tmps(addr->lhs) == true && addr->rhs->exp_type == CONSTANT){
				reg2 = (Tmp_s *)addr->lhs;
				cons = ((Constant *)addr->rhs)->val;
			}else if(is_tmps(addr->rhs) == true && addr->lhs->exp_type == CONSTANT){
				reg2 = (Tmp_s *)addr->rhs;
				cons = ((Constant *)addr->lhs)->val;
			}
		}else if(is_tmps(mem->addr)){
			reg2 = (Tmp_s *)mem->addr;
			cons = 0;
		}

		if(reg2 == 0 || cons == -1){
			return;
		}

		/*parameter got!*/
		/*begin checking*/
		for(i = 0; i < func_block->ptr_list.getsize(); i++){
			dptr * ptr = func_block->ptr_list.plist.at(i)->debug_info;
			if(ptr->cmp_loc(mem->addr, pc) == true){
				func_block->ptr_list.plist.at(i)->copy_list.push_back(reg1);
				return;
			}else{
				for(j = 0; j < func_block->ptr_list.plist.at(i)->copy_list.size(); j++){
					if(reg2->index == func_block->ptr_list.plist.at(i)->copy_list.at(j)->index){
						for(k = 0; k < func_block->ptr_list.plist.at(i)->child_list.size(); k++){
							pointer_info * child = func_block->ptr_list.plist.at(i)->child_list.at(k);
							bool cmp_res = cmp_offset(cons, child->debug_info);
							if(cmp_res == true){
								child->copy_list.push_back(reg1);
								return;
							}
						}
					}
				}
			}
		}


	}
};

//return the corresponding node of dptr* parent_ptr
int ptr_node_lookup(func_vertex_ptr func_block, dptr * parent_ptr, int offset){
	int k, w;
	for(k = 0; k < func_block->ptarget_list.size(); k++){
		for(w = 0; w < func_block->ptarget_list.at(k)->debug_info_list.size(); w++){
			dbase *child = func_block->ptarget_list.at(k)->debug_info_list.at(w);
			if(check_direct_child(parent_ptr, child) == true){
				bool res = cmp_offset(offset, child);
				if(res == true){
					return func_block->ptarget_list.at(k)->my_descriptor;
				}
			}
		}
	}

	/*check linklist*/
	for(k = 0; k < func_block->variable_list.size(); k++){
		if(check_child_from_parent(parent_ptr, func_block->variable_list.at(k)->debug_info) == true){
			bool res = cmp_offset(offset, func_block->variable_list.at(k)->debug_info);
			if(res == true){
				return func_block->variable_list.at(k)->my_descriptor;
			}
		}
	}

	return -1;
}

//check whether a exp correspond to a ptr
bool ptr_lookup(func_vertex_ptr func_block, Exp *exp, int block, int stmt, dptr*& ret_ptr, int *ret_cons){
	int i, j;
	Tmp_s *reg = 0;
	int cons = -1;

	if(exp->exp_type == BINOP){
		BinOp *addr = (BinOp *)exp;
		if(is_tmps(addr->lhs) == true && addr->rhs->exp_type == CONSTANT){
			reg = (Tmp_s *)addr->lhs;
			cons = ((Constant *)addr->rhs)->val;
		}else if(is_tmps(addr->rhs) == true && addr->lhs->exp_type == CONSTANT){
			reg = (Tmp_s *)addr->rhs;
			cons = ((Constant *)addr->lhs)->val;
		}
	}else if(is_tmps(exp) == true){
		reg = (Tmp_s *)exp;
		cons = 0;
	}

	if(reg == 0 || cons == -1){
		return false;
	}

	dptr * res = 0;
	for(i = 0; i < func_block->ptr_list.getsize(); i++){
		if(true == func_block->ptr_list.plist.at(i)->debug_info->cmp_loc(exp, func_block->stmt_block->block_list[block]->block[stmt]->asm_address)
				|| true == func_block->ptr_list.plist.at(i)->debug_info->cmp_loc(reg, func_block->stmt_block->block_list[block]->block[stmt]->asm_address)){
			res = func_block->ptr_list.plist.at(i)->debug_info;
		}else{
			for(j = 0; j < func_block->ptr_list.plist.at(i)->copy_list.size(); j++){
				if(reg->index == func_block->ptr_list.plist.at(i)->copy_list.at(j)->index){
					res = func_block->ptr_list.plist.at(i)->debug_info;
					break;
				}
			}
		}
		if(res != 0){
			ret_ptr = res;
			if(ret_cons != 0){
				*ret_cons = cons;
			}
			return true;
		}
	}

	return false;
}

//check whether a memory access corresponse to a pointed target (ptarget)
int ptarget_lookup(func_vertex_ptr func_block, Exp *exp, int block, int stmt){
	int i, j, k, w;
	int cons = -1;

	dptr * parent_ptr;
	bool result = ptr_lookup(func_block, exp, block, stmt, parent_ptr, &cons);
	if(result == false){
		return -1;
	}else{
		int vtd = ptr_node_lookup(func_block, parent_ptr, cons);
		if(vtd != -1){
			return vtd;
		}
	}

	return -1;
}

