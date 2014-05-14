#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>

#include "asm_program.h"
#include "disasm-pp.h"

extern "C" {
#include "libvex.h"
}

#include "irtoir.h"

/*include elf*/
#include <gelf.h>

#include "type_common.h"
#include "tmp_s.h"
#include "interproc.h"
#include "vine_api.h"

using namespace std;

int cfg_funclist_length;
struct addr_range* vine_text;

basic_block::~basic_block() {
	free(this->block);
}

func_block::~func_block() {
	int i;
	for (i = 0; i < this->len; i++) {
		delete this->block_list[i];
	}
	free(this->block_list);
}

fblock_ptr tranform_to_tmp_free(fblock_ptr func_blocks, int func_num) {
	int i, j, k;
	for (j = 0; j < func_blocks->len; j++) {
		for (k = 0; k < func_blocks->block_list[j]->blen; k++) {
			switch (func_blocks->block_list[j]->block[k]->stmt_type) {
			case MOVE: {
				//Left
				if (((Move *) func_blocks->block_list[j]->block[k])->lhs->exp_type == TEMP && check_tmp((Temp *) ((Move *) func_blocks->block_list[j]->block[k])->lhs) == YES) {
					//Do nothing, since this situation is "Temp = Exp" form.
				} else {
					visit_tmp((Exp *) func_blocks->block_list[j]->block[k], ((Move *) func_blocks->block_list[j]->block[k])->lhs, M_L, j, k, func_blocks);
				}

				//Right
				if (((Move *) func_blocks->block_list[j]->block[k])->rhs->exp_type == TEMP && check_tmp((Temp *) ((Move *) func_blocks->block_list[j]->block[k])->rhs) == YES) {
					Exp *tmp = query_value(func_blocks, j, k - 1, (Temp *) ((Move *) func_blocks->block_list[j]->block[k])->rhs);
					((Move *) func_blocks->block_list[j]->block[k])->rhs = tmp;
				} else {
					visit_tmp((Exp *) func_blocks->block_list[j]->block[k], ((Move *) func_blocks->block_list[j]->block[k])->rhs, M_R, j, k, func_blocks);
				}

				break;
			}
			case JMP: {

				if (((Jmp *) func_blocks->block_list[j]->block[k])->target->exp_type == TEMP && check_tmp((Temp *) ((Jmp *) func_blocks->block_list[j]->block[k])->target) == YES) {
					Exp *tmp = query_value(func_blocks, j, k - 1, (Temp *) ((Jmp *) func_blocks->block_list[j]->block[k])->target);
					((Jmp *) func_blocks->block_list[j]->block[k])->target = tmp;
				} else {
					visit_tmp((Exp *) func_blocks->block_list[j]->block[k], ((Jmp *) func_blocks->block_list[j]->block[k])->target, T_EXP, j, k, func_blocks);
				}

				break;
			}
			case CJMP: {
				if (((CJmp *) func_blocks->block_list[j]->block[k])->t_target->exp_type == TEMP && check_tmp((Temp *) ((CJmp *) func_blocks->block_list[j]->block[k])->t_target) == YES) {
					Exp *tmp = query_value(func_blocks, j, k - 1, (Temp *) ((CJmp *) func_blocks->block_list[j]->block[k])->t_target);
					((CJmp *) func_blocks->block_list[j]->block[k])->t_target = tmp;
				} else {
					visit_tmp((Exp *) func_blocks->block_list[j]->block[k], ((CJmp *) func_blocks->block_list[j]->block[k])->t_target, T_T, j, k, func_blocks);
				}

				if (((CJmp *) func_blocks->block_list[j]->block[k])->f_target->exp_type == TEMP && check_tmp((Temp *) ((CJmp *) func_blocks->block_list[j]->block[k])->f_target) == YES) {
					Exp *tmp = query_value(func_blocks, j, k - 1, (Temp *) ((CJmp *) func_blocks->block_list[j]->block[k])->f_target);
					((CJmp *) func_blocks->block_list[j]->block[k])->f_target = tmp;
				} else {
					visit_tmp((Exp *) func_blocks->block_list[j]->block[k], ((CJmp *) func_blocks->block_list[j]->block[k])->f_target, T_F, j, k, func_blocks);
				}

				if (((CJmp *) func_blocks->block_list[j]->block[k])->cond->exp_type == TEMP && check_tmp((Temp *) ((CJmp *) func_blocks->block_list[j]->block[k])->cond) == YES) {
					Exp *tmp = query_value(func_blocks, j, k - 1, (Temp *) ((CJmp *) func_blocks->block_list[j]->block[k])->cond);
					((CJmp *) func_blocks->block_list[j]->block[k])->cond = tmp;
				} else {
					visit_tmp((Exp *) func_blocks->block_list[j]->block[k], ((CJmp *) func_blocks->block_list[j]->block[k])->cond, T_C, j, k, func_blocks);
				}

				break;
			}
			default:
				break;

			}
		}
	}

	return func_blocks;
}

//Get the value of a certain temp variable
//value = an expression of register and constants
Exp *query_value(fblock_ptr func_block, int block_num, int stmt_num, Temp* t_name) {
//	find the latest definition (Move) of <t_name>
	int i;
	Exp *result;
	BOOL flag = NO;
	if (stmt_num >= func_block->block_list[block_num]->blen) {
		print_error("Current position out of range");
		printf("Look for <%s>\n", t_name->name.c_str());
		printf("In function <%s> BBlock[%d]:\n", func_block->func->name.c_str(), block_num);
		printf("Current position = %d\n", stmt_num);
		printf("Range:%d\n", func_block->block_list[block_num]->blen);
		exit(1);
	}

	for (i = stmt_num; i >= 0; i--) {
		if (i < 0) {
			break;
		}
		if (func_block->block_list[block_num]->block[i]->stmt_type == MOVE) {
			if (((Move *) func_block->block_list[block_num]->block[i])->lhs->exp_type == TEMP) {
				if (((Temp *) ((Move *) func_block->block_list[block_num]->block[i])->lhs)->name == t_name->name) {
					result = (Temp *) ((Move *) func_block->block_list[block_num]->block[i])->rhs;
					flag = YES;
					break;
				}
			}
		}
	}

	if (flag == NO && block_num - 1 >= 0) {
		result = query_value(func_block, block_num - 1, (func_block->block_list[block_num - 1]->blen) - 1, t_name);
	}

	return result;
}

void visit_tmp(Exp *parent, Exp *exp, EXP_OPT opt, int block_num, int curr_pos, fblock_ptr func_block) {
	if (exp->exp_type == BINOP) {
		visit_tmp(exp, ((BinOp *) exp)->lhs, LEXP, block_num, curr_pos, func_block);
		visit_tmp(exp, ((BinOp *) exp)->rhs, REXP, block_num, curr_pos, func_block);
	} else if (exp->exp_type == UNOP) {
		visit_tmp(exp, ((UnOp *) exp)->exp, EXP, block_num, curr_pos, func_block);
	} else if (exp->exp_type == CAST) {
		visit_tmp(exp, ((Cast *) exp)->exp, CAST_EXP, block_num, curr_pos, func_block);
	} else if (exp->exp_type == MEM) {
		visit_tmp(exp, ((Mem *) exp)->addr, ADDR, block_num, curr_pos, func_block);
	} else if (exp->exp_type == TEMP && check_tmp((Temp *) exp) == YES) {
		if (parent == NULL) {
			print_error("No parent for a Temp");
			exit(1);
		} else if (opt == NO_OPT) {
			print_error("No option for a Temp");
			exit(1);
		}
		Exp *tmp = query_value(func_block, block_num, curr_pos - 1, (Temp *) exp);
		switch (opt) {
		case LEXP: {
			((BinOp *) parent)->lhs = tmp;
			//printf("\t%s\n", ((BinOp *) parent)->lhs->tostring().c_str());
			break;
		}
		case REXP: {
			((BinOp *) parent)->rhs = tmp;
			//printf("\t%s\n", ((BinOp *) parent)->rhs->tostring().c_str());
			break;
		}
		case EXP: {
			((UnOp *) parent)->exp = tmp;
			//printf("\t%s\n", ((UnOp *) parent)->exp->tostring().c_str());
			break;
		}
		case ADDR: {
			((Mem *) parent)->addr = tmp;
			//printf("\t%s\n", ((Mem *) parent)->addr->tostring().c_str());
			break;
		}
		case CAST_EXP: {
			((Cast *) parent)->exp = tmp;
			//printf("\t%s\n", ((Cast *) parent)->exp->tostring().c_str());
			break;
		}
		default:
			break;
		}

	}

}

//Check whether a Temp* is a Tmp (rather than a variable or register)
BOOL check_tmp(Temp * tmp) {
	BOOL result = NO;
	if (tmp->name.compare(0, 2, "T_") == 0) {
		result = YES;
	}
	return result;
}

BOOL trans_to_vineir(char *filename, vector<vine_block_t *> &vine_blocks, asm_program_t * &asmprog) {
	BOOL res = NO;
	int block_count;
	int i, j;
	int k = 0;
	int flag = 0;
	int stmt_count = 0;
	int func_count = 0;
	int fb_count = 0;

	//
	// Disassemble the program
	//
	cerr << "Disassembling binary." << endl;
	asm_program_t *prog = new asm_program_t;
	prog = disassemble_program(filename);
	assert(prog);

	//
	// Translate asm to VEX IR
	//
	cerr << "Translating asm to VEX IR." << endl;
	vine_blocks = generate_vex_ir(prog);

	//
	// Translate VEX IR to Vine IR
	//
	cerr << "Translating VEX IR to Vine IR." << endl;
	vine_blocks = generate_vine_ir(prog, vine_blocks);

	//Comment some stmts that will trigger error or indirect jmp
	cerr << "Comment unreachable Jmps and errors." << endl;
	printf("Vine IR finished, %d blocks\n", vine_blocks.size());

	if (prog != 0 && vine_blocks.size() >= 0) {
		asmprog = prog;
		res = YES;
	}
	return res;
}

fblock_ptr transform_to_ssa(vector<vine_block_t *> vine_blocks, asm_program_t * prog, int func_num, struct addr_range *text) {

	vine_text = new struct addr_range();
	vine_text->high_addr = text->high_addr;
	vine_text->low_addr = text->low_addr;

	int i, j, k;
	int cfg_funclist_length;
	int func_count = 0;
	map<address_t, asm_function_t *>::const_iterator itr;
	int tmp_counter = 0;
	fblock_ptr function_list = new struct func_block();
	function_list->len = 0;
	function_list->block_list = NULL;

	if (vine_blocks.at(func_num)->vine_ir->size() == 0) {
		return function_list;
	}

	//    Move tmp to newly defined data structure
	//

	//	function block
	//
	for (itr = prog->functions.begin(); itr != prog->functions.end(); itr++) {
		if (tmp_counter == func_num) {
			break;
		}
		tmp_counter++;
	}
	function_list->func = itr->second;

	//    Move to new structure (Basic block)
	//
	cfg_funclist_length = prog->functions.size();
	if (func_num < cfg_funclist_length - 1) {
		itr++;
		to_basic_block(vine_blocks, function_list, itr->second->start_addr);
	} else if (func_num == cfg_funclist_length - 1) {
		to_basic_block(vine_blocks, function_list, vine_blocks.at(vine_blocks.size() - 1)->inst->address);
	}

	if (function_list->len == 0) {
		return function_list;
	}

	//From Temp to Tmp_s
	renew_tmp(function_list);

	//Add comment to (C)Jmp and Special
	add_comment(function_list);

	//Add additional comments for those (C)Jmp stmts who cannot find traget inside of the same function
//	for (j = 0; j < function_list->len - 3; j++) {
//		for (k = 0; k < function_list->block_list[j]->blen; k++) {
//			switch (function_list->block_list[j]->block[k]->stmt_type) {
//			case JMP: {
//				add_comment_jmp_inside(function_list, j, k,
//						((Jmp *) function_list->block_list[j]->block[k])->target);
//				break;
//			}
//			case CJMP: {
//				add_comment_jmp_inside(function_list, j, k,
//						((CJmp *) function_list->block_list[j]->block[k])->f_target);
//				add_comment_jmp_inside(function_list, j, k,
//						((CJmp *) function_list->block_list[j]->block[k])->t_target);
//				break;
//			}
//			default:
//				break;
//			}
//		}
//	}

	//	Construct control flow graph
	//
	cerr << "Construct control flow graph" << endl;
	build_cfg(function_list);
	prune_cfg(function_list);

	cerr << "Construct Phi nodes" << endl;
	printf("Number of funcions: %d\n", cfg_funclist_length);

	//    Add Phi nodes
	//
	add_phi(function_list);
	set_value(function_list);
	set_phi_para(function_list);

//	check blen
	for (j = 0; j < function_list->len; j++) {
		for (k = 0; k < function_list->block_list[j]->blen; k++) {
			if (check_stmt_type(function_list->block_list[j]->block[k]->stmt_type) == NO) {
				function_list->block_list[j]->blen = k - 1;
			}
		}
	}

	draw_graph(function_list, function_list->len);

	return function_list;

}

void add_edge_jmp(fblock_ptr func_block, Exp *target, int id) {
	int block_count = func_block->len;
	if (target->exp_type == NAME) {
		int index = search_lable(func_block, ((Name *) target)->name);
		if (index >= 0) {
			func_block->block_list[id]->child_next = index;
		} else {
			/*dynamic functin call*/
			/*point to next stmt*/
			//func_block->block_list[id]->child_next = block_count - 1;
			func_block->block_list[id]->child_next = id + 1;
		}
	} else if (target->exp_type == TEMP) {
		/*Point to BB_indrect*/
		/*solve indirect jump problem later!*/
		func_block->block_list[id]->child_next = block_count - 2;
	}
}

void add_edge_cjmp(fblock_ptr func_block, Exp *target, int id, TARGET opt) {
	int block_count = func_block->len;
	if (target->exp_type == NAME) {
		int index = search_lable(func_block, ((Name *) target)->name);
		if (index > 0) {
			if (opt == C_F) {
				func_block->block_list[id]->child_next = index;
			} else if (opt == C_T) {
				func_block->block_list[id]->child_jmp = index;
			}

		} else {
			if (opt == C_F) {
				func_block->block_list[id]->child_next = id + 1;
			} else if (opt == C_T) {
				func_block->block_list[id]->child_jmp = id + 1;
				//block_count - 1;
			}
		}
	} else if (target->exp_type == TEMP) {
		/*Point to BB_indrect*/
		/*solve indirect jump problem later!*/
		if (opt == C_F) {
			func_block->block_list[id]->child_next = block_count - 2;
		} else if (opt == C_T) {
			func_block->block_list[id]->child_jmp = block_count - 2;
		}

	}
}

int search_lable(fblock_ptr func_block, string lable) {
	int i, j;
	int result = -1;
	for (i = 1; i < func_block->len - 3; i++) {
		if (func_block->block_list[i]->type == BLOCK) {
			for (j = 0; j < func_block->block_list[i]->blen; j++) {
				if ((func_block->block_list[i]->block[j])->stmt_type == LABEL) {
					if (((Label *) func_block->block_list[i]->block[j])->label == lable) {
						result = i;
					}
				}
			}
		} else {
			//printf("Function %s : Block %d:\n",func_block->func->name.c_str(),i);
			switch (func_block->block_list[i]->type) {
			case ENTRY: {
				//printf("Node %d is ENTRY\n",i);
				break;
			}
			case EXIT: {
				//printf("Node %d is EXIT\n",i);
				break;
			}
			case INDI: {
				//printf("Node %d is INDI\n",i);
				break;
			}
			case ERROR: {
				//printf("Node %d is ERROR\n",i);
				break;
			}
			default: {
				//printf("Node %d is unknown\n",i);
				break;
			}
			}

		}
	}

	return result;
}

void print_edges(fblock_ptr func_block) {
	/*Print all cfg edges one by one*/
	int i, j;
	//printf("nodelist size = %d\n",nodelist.size());
	for (i = 0; i < func_block->len; i++) {
		switch (func_block->block_list[i]->branch_type) {
		case BIN: {
			cout << print_nodename(func_block->block_list, i);
			cout << " -> ";
			cout << print_nodename(func_block->block_list, func_block->block_list[i]->child_jmp) << endl;

			cout << print_nodename(func_block->block_list, i);
			cout << " -> ";
			cout << print_nodename(func_block->block_list, func_block->block_list[i]->child_next) << endl;
			break;
		}
		case UN: {
			cout << print_nodename(func_block->block_list, i);
			cout << " -> ";
			cout << print_nodename(func_block->block_list, func_block->block_list[i]->child_next) << endl;
			break;
		}
		case UNKNOW: {
			//printf("UNKNOW\n");
			break;
		}
		default:
			break;
		}
	}
}

string print_nodename(struct basic_block ** nodelist, int i) {
	string name;
	if (i < 0) {
		print_error("Node cannot be printed\n");
		return "<NULL>";
	}
	struct basic_block *node = nodelist[i];

	switch (node->type) {
	case BLOCK: {
		char tmp[256];
		string num;
		sprintf(tmp, "%d", i);
		num.assign(tmp);
		name = "BB_" + num;
		break;
	}
	case ENTRY: {
		name = "BB_Entry";
		break;
	}
	case EXIT: {
		name = "BB_Exit";
		break;
	}
	case INDI: {
		name = "BB_Indirect";
		break;
	}
	case ERROR: {
		name = "BB_Error";
		break;
	}
	default:
		break;
	}

	return name;
}

int get_size(stmt_type_t type) {
	int result = 0;
	switch (type) {
	case JMP: {
		result = sizeof(Jmp);
		break;
	}
	case CJMP: {
		result = sizeof(CJmp);
		break;
	}
	case SPECIAL: {
		result = sizeof(Special);
		break;
	}
	case MOVE: {
		result = sizeof(Move);
		break;
	}
	case COMMENT: {
		result = sizeof(Comment);
		break;
	}
	case LABEL: {
		result = sizeof(Label);
		break;
	}
	case EXPSTMT: {
		result = sizeof(Exp);
		break;
	}
	case VARDECL: {
		result = sizeof(VarDecl);
		break;
	}
	case CALL: {
		result = sizeof(Call);
		break;
	}
	case RETURN: {
		result = sizeof(Return);
		break;
	}
	case FUNCTION: {
		result = sizeof(Func);
		break;
	}
	case ASSERT: {
		result = sizeof(Assert);
		break;
	}

	default:
		break;
	}
	return result;
}

int count_block(vector<vine_block_t *> vine_blocks, int begin, int end) {
	int result = 1;
	int i, j;
	for (i = begin; i <= end; i++) {
		for (j = 0; j < vine_blocks.at(i)->vine_ir->size(); j++) {
			if (vine_blocks.at(i)->vine_ir->at(j)->stmt_type == JMP || vine_blocks.at(i)->vine_ir->at(j)->stmt_type == CJMP || vine_blocks.at(i)->vine_ir->at(j)->stmt_type == SPECIAL) {
				if (j == vine_blocks.at(i)->vine_ir->size() - 1 && i == end) {
					/*last stms, don't divide.*/
				} else {
					//printf("\tdivide at %s\n",vine_blocks.at(i)->vine_ir->at(j)->tostring().c_str());
					result++;
				}

			} else if (j + 1 < vine_blocks.at(i)->vine_ir->size()) {
				if (vine_blocks.at(i)->vine_ir->at(j + 1)->stmt_type == LABEL) {
					if (((Label *) vine_blocks.at(i)->vine_ir->at(j + 1))->label.compare(0, 2, "L_") == 0) {
						//printf("\tdivide at %s\n",vine_blocks.at(i)->vine_ir->at(j+1)->tostring().c_str());
						result++;
					}
				}
			}
		}
	}
	return result;
}

//Count the number of stmts from (i,j) to the next position to divide
int get_blen(vector<vine_block_t *> vine_blocks, int i, int j, int end) {
	int count = 0;
	int block, st;
	for (block = i; block < vine_blocks.size() && block <= end; block++) {
		for (st = (block == i ? j : 0); st < vine_blocks.at(block)->vine_ir->size(); st++) {
			count++;
			if (vine_blocks.at(block)->vine_ir->at(st)->stmt_type == JMP || vine_blocks.at(block)->vine_ir->at(st)->stmt_type == CJMP || vine_blocks.at(block)->vine_ir->at(st)->stmt_type == SPECIAL) {
				return count;
			} else if (st + 1 < vine_blocks.at(block)->vine_ir->size()) {
				if (((Label *) vine_blocks.at(block)->vine_ir->at(st + 1))->label.compare(0, 2, "L_") == 0) {
					return count;
				}
			}
		}
	}
	return count;
}

asm_function_t * get_func_name(asm_program_t *prog, vector<vine_block_t *> vine_blocks, int id) {
	asm_function_t * result = NULL;
	address_t i = vine_blocks.at(id)->inst->address;
	result = prog->functions.find(i)->second;
	assert(result != NULL);
	return result;
}

void renew_tmp(fblock_ptr func_block) {
	int i, j;
	for (i = 0; i < func_block->len; i++) {
		for (j = 0; j < func_block->block_list[i]->blen; j++) {
			switch (func_block->block_list[i]->block[j]->stmt_type) {
			case MOVE: {
				if (((Move *) func_block->block_list[i]->block[j])->lhs->exp_type == TEMP && get_reg_position(((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs)->name) != -1) {
					Tmp_s *tmp = new Tmp_s(((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs), -1);
					(((Move *) func_block->block_list[i]->block[j]))->lhs = tmp;
				} else {
					switch_to_tmps((Exp *) func_block->block_list[i]->block[j], ((Move *) func_block->block_list[i]->block[j])->lhs, M_L);
				}
				if (((Move *) func_block->block_list[i]->block[j])->rhs->exp_type == TEMP && get_reg_position(((Temp *) ((Move *) func_block->block_list[i]->block[j])->rhs)->name) != -1) {
					Tmp_s *tmp = new Tmp_s(((Temp *) ((Move *) func_block->block_list[i]->block[j])->rhs), -1);
					(((Move *) func_block->block_list[i]->block[j]))->rhs = tmp;
				} else {
					switch_to_tmps((Exp *) func_block->block_list[i]->block[j], ((Move *) func_block->block_list[i]->block[j])->rhs, M_R);
				}
				break;
			}
			case JMP: {
				if (((Jmp *) func_block->block_list[i]->block[j])->target->exp_type == TEMP && get_reg_position(((Temp *) ((Jmp *) func_block->block_list[i]->block[j])->target)->name) != -1) {
					Tmp_s *tmp = new Tmp_s(((Temp *) ((Jmp *) func_block->block_list[i]->block[j])->target), -1);
					(((Jmp *) func_block->block_list[i]->block[j]))->target = tmp;
				} else {
					switch_to_tmps((Exp *) func_block->block_list[i]->block[j], ((Jmp *) func_block->block_list[i]->block[j])->target, T_EXP);
				}
				break;
			}
			case CJMP: {
				if (((CJmp *) func_block->block_list[i]->block[j])->t_target->exp_type == TEMP && get_reg_position(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->t_target)->name) != -1) {
					Tmp_s *tmp = new Tmp_s(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->t_target), -1);
					(((CJmp *) func_block->block_list[i]->block[j]))->t_target = tmp;
				} else {
					switch_to_tmps((Exp *) func_block->block_list[i]->block[j], ((CJmp *) func_block->block_list[i]->block[j])->t_target, T_T);
				}
				if (((CJmp *) func_block->block_list[i]->block[j])->f_target->exp_type == TEMP && get_reg_position(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->f_target)->name) != -1) {
					Tmp_s *tmp = new Tmp_s(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->f_target), -1);
					(((CJmp *) func_block->block_list[i]->block[j]))->f_target = tmp;
				} else {
					switch_to_tmps((Exp *) func_block->block_list[i]->block[j], ((CJmp *) func_block->block_list[i]->block[j])->f_target, T_F);
				}
				break;
			}
			default:
				break;
			}
		}
	}
}

void switch_to_tmps(Exp *parent, Exp *exp, EXP_OPT opt) {
	if (exp->exp_type == BINOP) {
		switch_to_tmps(exp, ((BinOp *) exp)->lhs, LEXP);
		switch_to_tmps(exp, ((BinOp *) exp)->rhs, REXP);
	} else if (exp->exp_type == UNOP) {
		switch_to_tmps(exp, ((UnOp *) exp)->exp, EXP);
	} else if (exp->exp_type == CAST) {
		switch_to_tmps(exp, ((Cast *) exp)->exp, CAST_EXP);
	} else if (exp->exp_type == MEM) {
		switch_to_tmps(exp, ((Mem *) exp)->addr, ADDR);
	} else if (exp->exp_type == TEMP && get_reg_position(((Temp *) exp)->name) != -1) {
		if (parent == NULL) {
			print_error("No parent for a Temp");
			exit(1);
		} else if (opt == NO_OPT) {
			print_error("No option for a Temp");
			exit(1);
		}
		Tmp_s *tmp = new Tmp_s((Temp *) exp, -1);
		switch (opt) {
		case LEXP: {
			((BinOp *) parent)->lhs = tmp;
			//printf("\tSwitch %s\n", ((BinOp *) parent)->lhs->tostring().c_str());
			break;
		}
		case REXP: {
			((BinOp *) parent)->rhs = tmp;
			//printf("\tSwitch %s\n", ((BinOp *) parent)->rhs->tostring().c_str());
			break;
		}
		case EXP: {
			((UnOp *) parent)->exp = tmp;
			//printf("\tSwitch %s\n", ((UnOp *) parent)->exp->tostring().c_str());
			break;
		}
		case ADDR: {
			((Mem *) parent)->addr = tmp;
			//printf("\tSwitch %s\n", ((Mem *) parent)->addr->tostring().c_str());
			break;
		}
		case CAST_EXP: {
			((Cast *) parent)->exp = tmp;
			//printf("\tSwitch %s\n", ((Cast *) parent)->exp->tostring().c_str());
			break;
		}
		default: {
			//printf("A Temp without OPT: Don't switch to tmp\n");
			break;
		}
		}

	}

}

void build_cfg(fblock_ptr func_block) {
	int i, j;
	int stmt_count = 0;
	int flag = 0;

	for (i = 0; i < func_block->len; i++) {
		if (func_block->block_list[i]->type == BLOCK) {
			stmt_count = func_block->block_list[i]->blen;
			flag = 0;
			for (j = 0; j < stmt_count; j++) {
				//Stmt *buff = cfg_nodelist[i]->block->vine_ir->at(j);
				switch (func_block->block_list[i]->block[j]->stmt_type) {
				case CJMP: {
					//printf("block %d : stms %d cjmp\n",i, j);
					func_block->block_list[i]->branch_type = BIN;
					flag = 1;
					//CJmp *buff_cjmp = (CJmp *)buff->clone();
					/*!!different size cast!!*/
					add_edge_cjmp(func_block, ((CJmp *) func_block->block_list[i]->block[j])->t_target, i, C_T);
					add_edge_cjmp(func_block, ((CJmp *) func_block->block_list[i]->block[j])->f_target, i, C_F);
					break;
				}
				case JMP: {
					//printf("block %d : stms %d jmp\n",i, j);
					func_block->block_list[i]->branch_type = UN;
					flag = 1;
					//Jmp *buff_jmp = (Jmp *)buff->clone();
					add_edge_jmp(func_block, ((Jmp *) func_block->block_list[i]->block[j])->target, i);
					break;
				}
				case SPECIAL: {
					func_block->block_list[i]->branch_type = UN;
					flag = 1;
					//func_block->block_list[i]->child_next = func_block->len - 1;
					func_block->block_list[i]->child_next = i + 1;
					break;
				}
				default:
					break;
				}
				if (j == stmt_count - 1 && flag == 0) {
					func_block->block_list[i]->branch_type = UN;
					func_block->block_list[i]->child_next = i + 1;
				}
			}
		}
	}

	/*Add edge to EXIT*/
	func_block->block_list[func_block->len - 4]->branch_type = UN;
	func_block->block_list[func_block->len - 4]->child_next = func_block->len - 3;
}

void to_basic_block(vector<vine_block_t *> vine_blocks, fblock_ptr func_block, address_t end) {

	int begin_pos = -1;
	int end_pos = -1;
	int i, j;
	int block_count = 0;
	int k = 0;
	int stmt_count = 0;

	address_t begin = func_block->func->start_addr;

	for (i = 0; i < vine_blocks.size(); i++) {
		if (vine_blocks.at(i)->inst->address == begin) {
			begin_pos = i;
		}
		if (vine_blocks.at(i)->inst->address == end) {
			if (end == vine_blocks.at(vine_blocks.size() - 1)->inst->address || end == begin) {
				end_pos = i;
			} else {
				end_pos = i - 1;
			}
		}
	}

	//printf("begin: (%d)%d\n",begin_pos,vine_blocks.at(begin_pos)->inst->address);
	//printf("end: (%d):%d\n",end_pos, vine_blocks.at(end_pos)->inst->address);
	if (begin_pos == -1 || end_pos == -1 || begin_pos > end_pos) {

		print_error("Fail to map from address to position");
		exit(1);
	}

	block_count = count_block(vine_blocks, begin_pos, end_pos);
	func_block->len = block_count + 4;
	//printf("\t%d blocks of BB\n",func_block->len);
	func_block->block_list = (bblock_ptr *) malloc(func_block->len * sizeof(bblock_ptr));

	/*initialize each basic block in this function*/
	for (i = 0; i < func_block->len; i++) {
		//func_block->block_list[i] = (bblock_ptr) malloc(sizeof(struct basic_block));
		func_block->block_list[i] = new struct basic_block();
		func_block->block_list[i]->blen = 0;
		func_block->block_list[i]->child_jmp = -1;
		func_block->block_list[i]->child_next = -1;
	}

	/*Push all nodes to CFG*/
	/*push every block to cfg_nodelist*/

	/*Built Entry node*/
	func_block->block_list[k]->type = ENTRY;
	func_block->block_list[k]->branch_type = UN;
	func_block->block_list[k]->child_next = 1;
	func_block->block_list[k]->blen = 0;
	k++;

	func_block->block_list[k]->blen = get_blen(vine_blocks, begin_pos, 0, end_pos);
	//printf("\t%block[%d]\t%d stmts\n",0,func_block->block_list[0]->blen);
	func_block->block_list[k]->branch_type = UNKNOW;
	func_block->block_list[k]->type = BLOCK;
	func_block->block_list[k]->block = (Stmt **) malloc((func_block->block_list[k]->blen + REGMAX) * sizeof(Stmt*));

	for (i = begin_pos; i <= end_pos; i++) {
		for (j = 0; j < vine_blocks.at(i)->vine_ir->size(); j++) {
			if (func_block->block_list[k]->blen == stmt_count) {
				k++;
				stmt_count = 0;
				func_block->block_list[k]->func = func_block->func;
				func_block->block_list[k]->blen = get_blen(vine_blocks, i, j, end_pos);
				//printf("\t%block[%d]\t%d stmts\n",k,func_block->block_list[k]->blen);
				func_block->block_list[k]->branch_type = UNKNOW;
				func_block->block_list[k]->type = BLOCK;
				func_block->block_list[k]->block = (Stmt **) malloc((func_block->block_list[k]->blen + REGMAX) * sizeof(Stmt*));
			}
			func_block->block_list[k]->block[stmt_count] = vine_blocks.at(i)->vine_ir->at(j);
			stmt_count++;
		}
	}

	k++;

	/*Built Exit nodes*/
	func_block->block_list[k]->type = EXIT;
	func_block->block_list[k]->branch_type = UNKNOW;
	func_block->block_list[k]->blen = 0;
	k++;

	//cout<<print_nodename(cfg_nodelist, cfg_nodelist_length -3)<<endl;
	/*Built indirect nodes*/
	func_block->block_list[k]->type = INDI;
	func_block->block_list[k]->branch_type = UNKNOW;
	func_block->block_list[k]->blen = 0;
	k++;

	/*Built error nodes*/
	func_block->block_list[k]->type = ERROR;
	func_block->block_list[k]->branch_type = UNKNOW;
	func_block->block_list[k]->blen = 0;
}

/*Remove certain block in func_block*/
void remove_bblock(fblock_ptr func_block, int target) {
	int i;
	//printf("remove block[%d] in function %s\n",target,func_block->func->name.c_str());
	if (target == func_block->len - 1) {
		func_block->len--;
	} else {
		for (i = target; i < func_block->len - 1; i++) {
			func_block->block_list[i] = func_block->block_list[i + 1];
		}
		func_block->len--;
	}

	for (i = 0; i < func_block->len; i++) {
		if (func_block->block_list[i]->branch_type == BIN) {
			if (func_block->block_list[i]->child_jmp > target) {
				func_block->block_list[i]->child_jmp--;
			}
			if (func_block->block_list[i]->child_next > target) {
				func_block->block_list[i]->child_next--;
			}
		} else if (func_block->block_list[i]->branch_type == UN) {
			if (func_block->block_list[i]->child_next > target) {
				func_block->block_list[i]->child_next--;
			}
		}
	}
}

/*Remove corresponding node in doms[]*/
/*Only use after remove_bblock()*/
void remove_dom(fblock_ptr func_block, int target) {
	int i;
	int len = func_block->len + 1; //Current length of doms[]
	for (i = target + 1; i < len; i++) {
		doms[i - 1].current_loop_processed = doms[i].current_loop_processed;
		doms[i - 1].idom_id = doms[i].idom_id;
		doms[i - 1].processed = doms[i].processed;
	}

	for (i = 0; i < func_block->len; i++) {
		if (doms[i].idom_id == target) {
			doms[i].idom_id = -1;
		}
		if (doms[i].idom_id > target) {
			doms[i].idom_id--;
		}
	}
}

/*Remove basic blocks (nodes) with no predecessor*/
void prune_cfg(fblock_ptr func_block) {
	int i;
	for (i = 1; i < func_block->len; i++) {
		if (predecessor_num_lookup(func_block, i) == 0) {
			remove_bblock(func_block, i);
			i--;
		}
	}
}

int predecessor_num_lookup(fblock_ptr func_block, int index) {
//	How many predecessors does the node func_block->block_list[index] have?
	int i;
	int count = 0;

	if (index == -1) {
		print_error("Index = -1 (invalid)");
		exit(1);
	}

	for (i = 0; i < func_block->len - 3; i++) {
		if (func_block->block_list[i]->child_jmp == index || func_block->block_list[i]->child_next == index) {
			count++;
		}
	}
	//printf("block %d has %d predecessors\n",index, count);
	return count;
}

void add_comment(fblock_ptr vine_blocks) {
	int i, j;

	for (i = 0; i < vine_blocks->len; i++) {
		for (j = 0; j < vine_blocks->block_list[i]->blen; j++) {
			switch (vine_blocks->block_list[i]->block[j]->stmt_type) {
			case JMP: {
				//cerr << "add_comment_jmp" << endl;
				add_comment_jmp(vine_blocks, i, j, ((Jmp *) vine_blocks->block_list[i]->block[j])->target);
				break;
			}
			case CJMP: {
				//cerr << "add_comment_jmp" << endl;
				add_comment_jmp(vine_blocks, i, j, ((CJmp *) vine_blocks->block_list[i]->block[j])->t_target);
				add_comment_jmp(vine_blocks, i, j, ((CJmp *) vine_blocks->block_list[i]->block[j])->f_target);
				break;
			}
			case SPECIAL: {
				//cerr << "add_comment_special" << endl;
				//comment_stmt(vine_blocks, i, j);
				Special *t_special = (Special *) vine_blocks->block_list[i]->block[j];
				if (t_special->special == "call") {
					/*don't all comment to call*/
				} else {
					comment_stmt(vine_blocks, i, j);
				}
				break;
			}
			default:
				break;
			}
		}
	}
}

/*void add_comment(fblock_ptr vine_blocks) {
 int i, j;
 for(i = 0; i < vine_blocks->len; i++){
 for(j = 0; j < vine_blocks->block_list[i]->blen; j++){
 switch (vine_blocks->block_list[i]->block[j]->stmt_type) {
 case JMP: {
 //cerr << "add_comment_jmp" << endl;
 add_comment_jmp(vine_blocks, i, j,
 ((Jmp *) vine_blocks->block_list[i]->block[j])->target);
 break;
 }
 case CJMP: {
 //cerr << "add_comment_jmp" << endl;
 add_comment_jmp(vine_blocks, i, j,
 ((CJmp *) vine_blocks->block_list[i]->block[j])->t_target);
 add_comment_jmp(vine_blocks, i, j,
 ((CJmp *) vine_blocks->block_list[i]->block[j])->f_target);
 break;
 }
 case SPECIAL: {
 //cerr << "add_comment_special" << endl;
 comment_stmt(vine_blocks, i, j);
 break;
 }
 default:
 break;
 }
 }
 }
 }*/

int search_single_block_for_lable(fblock_ptr vine_blocks, int block, string lable) {
	int i;
	int result = -1;
	for (i = 0; i < vine_blocks->block_list[block]->blen; i++) {
		if (vine_blocks->block_list[block]->block[i]->stmt_type == LABEL) {
			if (((Label *) vine_blocks->block_list[block]->block[i])->label == lable) {
				result = i;
				break;
			}
		}
	}

	return result;
}

int search_raw_blocks(fblock_ptr vine_blocks, string label, int current) {
	int result = -1;
	int i, j;

//	Look into next block
	result = search_single_block_for_lable(vine_blocks, current + 1, label);
	if (result != -1) {
		return result;
	}

//	Look into current block and blocks before current
	for (i = current; i >= 0; i--) {
		result = search_single_block_for_lable(vine_blocks, i, label);
		if (result != -1) {
			return result;
		}
	}

//	Look into blocks next to next block
	for (i = current + 2; i < vine_blocks->len; i++) {
		result = search_single_block_for_lable(vine_blocks, i, label);
		if (result != -1) {
			return result;
		}
	}

	return result;
}

void add_comment_jmp_inside(fblock_ptr func_block, int j, int k, Exp *target) {
	if (target->exp_type == NAME) {
		int index = search_lable(func_block, ((Name *) target)->name);
		if (index >= 0) {
			/*jmp to somewhere inside of this*/
			/*No need to comment*/
		} else {
			/*Error Jmp that jump to nowhere (indirect jump)*/
			comment_stmt_inside(func_block, j, k);
		}
	}
}

void add_comment_jmp(fblock_ptr vine_blocks, int i, int j, Exp *target) {
	address_t start_addr = vine_blocks->func->start_addr;
	address_t end_addr = vine_blocks->func->end_addr;

	if (target->exp_type == NAME) {
		string target_name = ((Name *) target)->name;
		if (target_name.substr(0, 2) == "L_") {
			int index = search_raw_blocks(vine_blocks, ((Name *) target)->name, i);
			if (index >= 0) {
				//No need to comment
			} else {
				//Error Jmp that jump to nowhere (indirect jump)
				comment_stmt(vine_blocks, i, j);
			}

		} else if (target_name.substr(0, 5) == "pc_0x") {
			address_t addr = name_to_hex(target_name);
			if (addr >= vine_text->low_addr && addr < vine_text->high_addr) {
				if (addr >= start_addr && addr < end_addr) {
					/*control flow inside of the same function*/
					/*no need to comment*/
				} else {
					/*static function call*/
					/*trans to comment temperately*/
					comment_stmt(vine_blocks, i, j);
				}
			} else {
				/*dynamic function call*/
				/*no need to comment*/
			}
		}
	} else if (target->exp_type == TEMP) {
		/*Indirect jmp*/
		/*Add comment*/
		comment_stmt(vine_blocks, i, j);
	}
}

void comment_stmt(fblock_ptr vine_blocks, int i, int j) {
	if (vine_blocks->block_list[i]->block[j]->stmt_type != COMMENT) {
		Comment *tmp = new Comment(vine_blocks->block_list[i]->block[j]->tostring(), vine_blocks->block_list[i]->block[j]->asm_address, vine_blocks->block_list[i]->block[j]->ir_address);
		vine_blocks->block_list[i]->block[j] = tmp;
	}
}

void comment_stmt_inside(fblock_ptr func_block, int j, int k) {
	if (func_block->block_list[j]->block[k]->stmt_type != COMMENT) {
		Comment *tmp = new Comment(func_block->block_list[j]->block[k]->tostring(), func_block->block_list[j]->block[k]->asm_address, func_block->block_list[j]->block[k]->ir_address);
		func_block->block_list[j]->block[k] = tmp;
	}
}

BOOL deep_first_search(fblock_ptr func_block, int current) {
	BOOL result = NO;
	BOOL tmp_1, tmp_2;
	if (current >= func_block->len) {
		print_error("DFS error, current position exceed largest block number");
	}

	/*Process current node*/
	int new_idom = get_predecessor(func_block, doms, 0, current);
	int next_predecessor = get_predecessor(func_block, doms, new_idom + 1, current);
	while (next_predecessor != -1) {
		if (doms[next_predecessor].processed == YES) {
			new_idom = intersect(doms, next_predecessor, new_idom);
		}
		next_predecessor = get_predecessor(func_block, doms, next_predecessor + 1, current);
	}

	if (doms[current].idom_id != new_idom) {
		doms[current].idom_id = new_idom;
		result = YES;
	}
	doms[current].processed = YES;
	doms[current].current_loop_processed = YES;

	/*Process branch(s)*/
	if (func_block->block_list[current]->branch_type == BIN) {
		if (doms[func_block->block_list[current]->child_jmp].current_loop_processed == NO) {
			tmp_1 = deep_first_search(func_block, func_block->block_list[current]->child_jmp);
		}
		if (doms[func_block->block_list[current]->child_next].current_loop_processed == NO) {
			tmp_2 = deep_first_search(func_block, func_block->block_list[current]->child_next);
		}

		if (tmp_1 == YES || tmp_2 == YES) {
			result = YES;
		}
	} else if (func_block->block_list[current]->branch_type == UN) {
		if (doms[func_block->block_list[current]->child_next].current_loop_processed == NO) {
			tmp_1 = deep_first_search(func_block, func_block->block_list[current]->child_next);
		}
		if (tmp_1 == YES) {
			result = YES;
		}
	}

	return result;
}

void add_phi(fblock_ptr func_block) {
	int i, j, k;
	BOOL flag;
	doms = (struct idom *) malloc((func_block->len) * sizeof(struct idom));
	//struct idom doms[func_block->len];

	for (i = 0; i < func_block->len; i++) {
		doms[i].processed = NO;
		doms[i].current_loop_processed = NO;
		doms[i].idom_id = -1;
	}
	doms[0].idom_id = 0;
	doms[0].processed = YES;
	doms[0].current_loop_processed = YES;

	BOOL changed = YES;
	while (changed == YES) {

		changed = deep_first_search(func_block, 1);

		/*Reset processed*/
		for (i = 0; i < func_block->len; i++) {
			doms[i].current_loop_processed = NO;
		}
	}
	//printf("Dom finished\n");
	//exit(1);

	//Pretty print this array;
	//printf("%s:\n",func_block->func->name.c_str());
	for (i = 0; i < func_block->len - 2; i++) {
		//printf("idom[BB_%d] = %d\n",i, doms[i].idom_id);
	}

	//draw_graph(func_block, func_block->len);
	/*Remove additional blocks that unreachable from start node*/
	for (i = 1; i < func_block->len; i++) {
		if (doms[i].idom_id == -1) {
			remove_bblock(func_block, i);
			remove_dom(func_block, i);
			i--;
		}
	}

	//Compute dominance frontier
	vector<int> df[func_block->len];
	for (i = 1; i < func_block->len; i++) {
		if (predecessor_num_lookup(func_block, i) >= 2) {
			int next_predecessor = get_predecessor(func_block, doms, 0, i);
			while (next_predecessor != -1) {
				//printf("next_predecessor:%d\n",next_predecessor);
				int runner = next_predecessor;
				//printf("runner = %d\n",runner);
				while (runner != doms[i].idom_id) {
					flag = YES;
					//printf("BB_%d has %d fd(s)\n",runner, df[runner].size());
					for (j = 0; j < df[runner].size(); j++) {
						if (df[runner].at(j) == i) {
							flag = NO;
						}
					}
					if (flag == YES && runner != i) {
						df[runner].push_back(i);
					}

					//printf("Add %d to df[%d]\n",i,runner);
					runner = doms[runner].idom_id;
				}
				next_predecessor = get_predecessor(func_block, doms, next_predecessor + 1, i);
			}
		}
	}

	//Add Phi nodes
	for (i = 0; i < func_block->len; i++) {
		for (j = 0; j < func_block->block_list[i]->blen; j++) {
			/*For each Move*/
			if (func_block->block_list[i]->block[j]->stmt_type == MOVE) {
				if (((Move *) func_block->block_list[i]->block[j])->lhs->exp_type == TEMP && get_reg_position(((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs)->name) != -1) {
					//Register changed
					//check exist Phi_s before Add new Phi_s
					for (k = 0; k < df[i].size(); k++) {
						if (check_duplicated_phi(func_block, df[i].at(k), ((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs)->name) == NO) {

							vector<Tmp_s*> v;
							Phi_s * right = new Phi_s(((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs)->name, v);
							Tmp_s * left = new Tmp_s((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs, -2);
							Move * stmt = new Move(left, right, 0x0, 0x0);
							//printf("[ %s| block %d] %s\n", func_block->func->name.c_str(), df[i].at(k), left->name.c_str());
							//printf("%s\t result:%d\n",((Temp *)((Move *)func_block->block_list[i]->block[j])->lhs)->name.c_str(),get_reg_position(((Temp *)((Move *)func_block->block_list[i]->block[j])->lhs)->name));
							//if(df[i].at(k) == i){printf("Error!\n");
							//printf("df[%d] = %d\n",i,df[i].at(k));}
							insert_stmt(func_block, df[i].at(k), 0, stmt);
						}
					}
				}
			}
		}
	}

	//draw_graph(func_block, func_block->len);
}

BOOL check_duplicated_phi(fblock_ptr func_block, int block, string name) {
	/*check whether there is phi point with the same name in block*/
	BOOL result = NO;
	int i;
	for (i = 0; i < func_block->block_list[block]->blen; i++) {
		if (func_block->block_list[block]->block[i]->stmt_type == MOVE) {
			if (((Move *) func_block->block_list[block]->block[i])->rhs->exp_type == PHI) {
				if (((Phi_s *) ((Move *) func_block->block_list[block]->block[i])->rhs)->phi_name == name) {
					result = YES;
					break;
				}
			}
		}
	}
	return result;
}

int intersect(struct idom *doms, int b1, int b2) {
	int finger1, finger2;
	finger1 = b1;
	finger2 = b2;
	//printf("bi = %d\tb2= %d\n",b1, b2);
	if (b1 == -1 || b2 == -1) {
		print_error("Error figner\n");
		exit(1);
	}
	while (finger1 != finger2 && finger1 != -1 && finger2 != -1) {
		while (finger1 > finger2 && finger1 >= 0 && finger2 >= 0) {
			finger1 = doms[finger1].idom_id;
			//printf("finger1 = %d\tfinger2 = %d\n",finger1, finger2);
		}
		while (finger2 > finger1 && finger1 >= 0 && finger2 >= 0) {
			finger2 = doms[finger2].idom_id;
			//printf("finger1 = %d\tfinger2 = %d\n",finger1, finger2);
		}
	}

	if (finger1 < 0 || finger2 < 0) {
		return -1;
	}

	return finger1;
}

/*Return the next processed predecessor starting from begin*/
/*Return -1 if no more predecessor exist*/
int get_predecessor(fblock_ptr func_block, struct idom *doms, int begin, int target) {
	int result = -1;
	int i;
	for (i = begin; i < func_block->len; i++) {
		if (doms[i].processed == YES) {
			if (func_block->block_list[i]->branch_type == BIN) {
				if (func_block->block_list[i]->child_jmp == target || func_block->block_list[i]->child_next == target) {
					result = i;
					break;
				}
			} else if (func_block->block_list[i]->branch_type == UN) {
				if (func_block->block_list[i]->child_next == target) {
					result = i;
					break;
				}
			}

		}
	}

	return result;
}

int get_normal_predecessor(fblock_ptr func_block, int begin, int target) {
	int result = -1;
	int i;
	for (i = begin; i < func_block->len; i++) {
		if (func_block->block_list[i]->branch_type == BIN) {
			if (func_block->block_list[i]->child_jmp == target || func_block->block_list[i]->child_next == target) {
				result = i;
				if (result == target) {
					result = -1;
				} else {
					break;
				}
			}
		} else if (func_block->block_list[i]->branch_type == UN) {
			if (func_block->block_list[i]->child_next == target) {
				result = i;
				if (result == target) {
					result = -1;
				} else {
					break;
				}
			}
		}
	}

	return result;
}

/*Insert a new stmt before func_block->block_list[block]->block[pos]*/
void insert_stmt(fblock_ptr func_block, int block, int pos, Stmt *insert) {
	int i;
	for (i = func_block->block_list[block]->blen; i > pos; i--) {
		func_block->block_list[block]->block[i] = func_block->block_list[block]->block[i - 1];
	}
	func_block->block_list[block]->blen++;
	func_block->block_list[block]->block[pos] = insert;
}

int get_reg_position(string reg_name) {
	int result = -1;
	int i;
	for (i = 0; i < REGMAX; i++) {
		if (str_reg[i] == reg_name) {
			result = i;
			break;
		}
	}
	return result;
}

void set_value(fblock_ptr func_block) {
	int i, j;
	int position;

//	initialize current number array and global counter
	for (i = 0; i < REGMAX; i++) {
		current_number[i] = i;
	}
	global_counter = i;

//	set value for all registers
	for (i = 0; i < func_block->len; i++) {
		for (j = 0; j < func_block->block_list[i]->blen; j++) {
			switch (func_block->block_list[i]->block[j]->stmt_type) {
			case SPECIAL: {
				/*Renew eax after each special("call")*/
				Special *sp = (Special *) func_block->block_list[i]->block[j];
				if (sp->special == "call") {
					global_counter++;
					current_number[R_EAX] = global_counter;
				}
				break;
			}
			case MOVE: {
				if (((Move *) func_block->block_list[i]->block[j])->rhs->exp_type == TEMP && get_reg_position(((Temp *) ((Move *) func_block->block_list[i]->block[j])->rhs)->name) != -1) {
					position = get_reg_position(((Temp *) ((Move *) func_block->block_list[i]->block[j])->rhs)->name);
					if (position == -1) {
						print_error("Invalid register name");
						exit(1);
					}
					if (current_number[position] == -1) {
						global_counter++;
						current_number[position] = global_counter;
					}
					((Tmp_s *) ((Temp *) ((Move *) func_block->block_list[i]->block[j])->rhs))->index = current_number[position];
				} else {
					set_exp_value(((Move *) func_block->block_list[i]->block[j])->rhs);
				}
				if (((Move *) func_block->block_list[i]->block[j])->lhs->exp_type == TEMP && get_reg_position(((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs)->name) != -1) {
					global_counter++;
					position = get_reg_position(((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs)->name);
					if (position == -1) {
						print_error("Invalid register name");
						exit(1);
					}
					current_number[position] = global_counter;
					((Tmp_s *) ((Temp *) ((Move *) func_block->block_list[i]->block[j])->lhs))->index = current_number[position];

				} else {
					set_exp_value(((Move *) func_block->block_list[i]->block[j])->lhs);
				}
				break;
			}
			case JMP: {
				if (((Jmp *) func_block->block_list[i]->block[j])->target->exp_type == TEMP && get_reg_position(((Temp *) ((Jmp *) func_block->block_list[i]->block[j])->target)->name) != -1) {
					position = get_reg_position(((Temp *) ((Jmp *) func_block->block_list[i]->block[j])->target)->name);
					if (position == -1) {
						print_error("Invalid register name");
						exit(1);
					}
					if (current_number[position] == -1) {
						global_counter++;
						current_number[position] = global_counter;
					}
					((Tmp_s *) ((Temp *) ((Jmp *) func_block->block_list[i]->block[j])->target))->index = current_number[position];
				} else {
					set_exp_value(((Jmp *) func_block->block_list[i]->block[j])->target);
				}
				break;
			}
			case CJMP: {
				if (((CJmp *) func_block->block_list[i]->block[j])->t_target->exp_type == TEMP && get_reg_position(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->t_target)->name) != -1) {
					position = get_reg_position(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->t_target)->name);
					if (position == -1) {
						print_error("Invalid register name");
						exit(1);
					}
					if (current_number[position] == -1) {
						global_counter++;
						current_number[position] = global_counter;
					}
					((Tmp_s *) ((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->t_target))->index = current_number[position];
				} else {
					set_exp_value(((CJmp *) func_block->block_list[i]->block[j])->t_target);
				}
				if (((CJmp *) func_block->block_list[i]->block[j])->f_target->exp_type == TEMP && get_reg_position(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->f_target)->name) != -1) {
					position = get_reg_position(((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->f_target)->name);
					if (position == -1) {
						print_error("Invalid register name");
						exit(1);
					}
					if (current_number[position] == -1) {
						global_counter++;
						current_number[position] = global_counter;
					}
					((Tmp_s *) ((Temp *) ((CJmp *) func_block->block_list[i]->block[j])->f_target))->index = current_number[position];
				} else {
					set_exp_value(((CJmp *) func_block->block_list[i]->block[j])->f_target);
				}
				break;
			}
			default:
				break;
			}
		}
	}
}

void set_exp_value(Exp *exp) {
	if (exp->exp_type == BINOP) {
		set_exp_value(((BinOp *) exp)->lhs);
		set_exp_value(((BinOp *) exp)->rhs);
	} else if (exp->exp_type == UNOP) {
		set_exp_value(((UnOp *) exp)->exp);
	} else if (exp->exp_type == CAST) {
		set_exp_value(((Cast *) exp)->exp);
	} else if (exp->exp_type == MEM) {
		set_exp_value(((Mem *) exp)->addr);
	} else if (exp->exp_type == TEMP && get_reg_position(((Temp *) exp)->name) != -1) {
		int position = get_reg_position(((Temp *) exp)->name);
		if (position == -1) {
			print_error("Invalid register name");
			exit(1);
		}
		if (current_number[position] == -1) {
			global_counter++;
			current_number[position] = global_counter;
		}
		((Tmp_s *) exp)->index = current_number[position];
	}

}

void set_phi_para(fblock_ptr func_block) {
	int i, j;
	int position;
	for (i = 0; i < func_block->len; i++) {
		for (j = 0; j < func_block->block_list[i]->blen; j++) {
			if (func_block->block_list[i]->block[j]->stmt_type == MOVE) {
				if (((Move *) func_block->block_list[i]->block[j])->rhs->exp_type == PHI) {
					position = get_reg_position(((Phi_s *) ((Move *) func_block->block_list[i]->block[j])->rhs)->phi_name);
					if (position != -1) {
						search_latest_assign(func_block, i, position, func_block->block_list[i]->block[j]);
					}
				}
			}
		}
	}
}

int search_latest_assign(fblock_ptr func_block, int target, int reg_num, Stmt *func) {
	int result;
	int i, j;

	int next_predecessor = get_normal_predecessor(func_block, 0, target);
	while (next_predecessor != -1 && next_predecessor != target) {
		//printf("next_predecessor = %d\n",next_predecessor);
		int next = next_predecessor;
		result = get_latest_from_bblock(func_block, next, reg_num);
		//printf("BB_%d %s\n",target,str_reg[reg_num].c_str());
		while (result == -1 && next != 0) {
			//printf("result = %d\n",result);
			next = doms[next].idom_id;
			//printf("next = %d\n",next);
			result = get_latest_from_bblock(func_block, next, reg_num);
		}
		if (next == 0) {
			//Unable to find from current position to start point
			//FIXME: why current number?
			//change to: position of the first SSA variable of this register
			//result = current_number[get_reg_position(((Tmp_s *) ((Move *) func)->lhs)->name)];
			result = get_reg_position(((Tmp_s *) ((Move *) func)->lhs)->name);
		}
		//printf("result = %d\n",result);
		//Check whether this parameter has been inserted
		if (((Phi_s *) ((Move *) func)->rhs)->check_duplicate_para(result) == 0) {
			Tmp_s * tmp = new Tmp_s(((Tmp_s *) ((Move *) func)->lhs)->typ, ((Tmp_s *) ((Move *) func)->lhs)->name, result);
			((Phi_s *) ((Move *) func)->rhs)->addVar(tmp);
		}

		next_predecessor = get_normal_predecessor(func_block, next_predecessor + 1, target);
	}
	return result;
}

unsigned long long name_to_hex(string name) {
	//string name: pc_0x80483fe -> hex number: 80483fe
	unsigned long long res = 0;
	std::stringstream str;
	string t_str = name.substr(5);
	str << t_str;
	str >> std::hex >> res;
	return res;

}

int get_latest_from_bblock(fblock_ptr func_block, int block, int reg_num) {
	int result = -1;
	int i;
	for (i = func_block->block_list[block]->blen - 1; i >= 0; i--) {
		if (func_block->block_list[block]->block[i]->stmt_type == MOVE) {
			if (((Move *) func_block->block_list[block]->block[i])->lhs->exp_type == TEMP) {
				if (((Temp *) ((Move *) func_block->block_list[block]->block[i])->lhs)->name == str_reg[reg_num]) {
					result = ((Tmp_s *) ((Temp *) ((Move *) func_block->block_list[block]->block[i])->lhs))->index;
					break;
				}
			}
		}
	}
	return result;
}

BOOL check_stmt_type(stmt_type_t type) {
	BOOL result = YES;
	if (type > ASSERT || type < JMP) {
		result = NO;
	}
	return result;
}

void print_error(string msg) {
	cout << "Error: ";
	cout << msg << endl;
}
