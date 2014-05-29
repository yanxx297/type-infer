#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>
#include <utility>
#include <stdbool.h>
#include <fcntl.h>

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
extern "C" {
#include "libvex.h"
}
#include "irtoir.h"

#include "type_common.h"
#include "location.h"
#include "tmp_s.h"
#include "dvar.h"
#include "vine_api.h"
#include "debug_info.h"
#include "vertex.h"

#include "type_dwarf_util.h"
#include "ptr_handler.h"
#include "debug_tool.h"
#include "infer.h"

using namespace std;

void dfs_min_cut(Graph::vertex_descriptor src, func_vertex_ptr func_block, Graph &g) {
	//walk from src

//	taint node
	boost::property_map<Graph, id_pos_type_t>::type g_id = boost::get(id_pos_type_t(), g);
	boost::property_map<Graph, boost::vertex_color_t>::type g_color = boost::get(boost::vertex_color, g);
	boost::property_map<Graph, boost::edge_residual_capacity_t>::type g_res = boost::get(boost::edge_residual_capacity, g);
	boost::property_map<Graph, visited_type_t>::type g_visited = boost::get(visited_type_t(), g);
	boost::property_map<Graph, signed_unsigend_type_t>::type g_sut = boost::get(signed_unsigend_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	g_color[src] = boost::red_color;
	g_visited[src] = true;

	if (g_vet[src] == VARIABLE) {
		func_block->variable_list.at(g_id[src])->infered_su = SIGNED_T;
	} else if (g_vet[src] == POINTED) {
		func_block->ptarget_list.at(g_id[src])->infered_su = SIGNED_T;
	} else if (g_vet[src] == OPERATION || g_vet[src] == REGISTER) {
		g_sut[src] = SIGNED_T;
	}

//	walk through children, recursively
	boost::graph_traits<Graph>::edge_iterator ei, ei_end;
	for (tie(ei, ei_end) = boost::edges(g); ei != ei_end; ++ei) {
		if (source(*ei, g) == src && g_visited[target(*ei, g)] != true) {
			if (g_res[*ei] > 0) {
				dfs_min_cut(target(*ei, g), func_block, g);
			}
		}
	}
}

////////////////////////////////////////////////////////////
//	Create graph
////////////////////////////////////////////////////////////

int reg_name_to_dwop(Temp * tmp) {
	int result = -1;
	if (tmp->name == "R_EAX") {
		result = DW_OP_breg0;
	} else if (tmp->name == "R_ECX") {
		result = DW_OP_breg1;
	} else if (tmp->name == "R_EDX") {
		result = DW_OP_breg2;
	} else if (tmp->name == "R_EBX") {
		result = DW_OP_breg3;
	} else if (tmp->name == "R_ESP") {
		result = DW_OP_breg4;
	} else if (tmp->name == "R_EBP") {
		result = DW_OP_breg5;
	} else if (tmp->name == "R_ESI") {
		result = DW_OP_breg6;
	} else if (tmp->name == "R_EDI") {
		result = DW_OP_breg7;
	} else if (tmp->name == "R_EIP") {
		result = DW_OP_breg8;
	} else if (tmp->name == "EFLAGS") {
		result = DW_OP_breg9;
	}

	return result;
}

//Given 2 nodes of an edge, check whether this edge is already in this graph g.
bool check_duplicated_edge(func_vertex_ptr func_list, int src_node, int des_node, Graph &g) {
	if (func_list->edge_list.count(pair<int, int>(src_node, des_node)) > 0) {
		return true;
	} else {
		return false;
	}
}

void print_capacity(Graph &g) {
	boost::property_map<Graph, boost::edge_capacity_t>::type capacity = boost::get(boost::edge_capacity, g);
	boost::property_map<Graph, boost::edge_residual_capacity_t>::type residual_capacity = boost::get(boost::edge_residual_capacity, g);

	boost::graph_traits<Graph>::vertex_iterator u_iter, u_end;
	boost::graph_traits<Graph>::out_edge_iterator ei, e_end;
	for (tie(u_iter, u_end) = vertices(g); u_iter != u_end; ++u_iter)
		for (tie(ei, e_end) = out_edges(*u_iter, g); ei != e_end; ++ei)
			if (capacity[*ei] > 0)
				std::cout << "Source: " << *u_iter << " destination: " << target(*ei, g) << " capacity: " << capacity[*ei] << "residual cap: " << residual_capacity[*ei] << " used capacity: " << (capacity[*ei] - residual_capacity[*ei]) << std::endl;
}

Traits::edge_descriptor add_edge_with_cap(func_vertex_ptr func_list, Traits::vertex_descriptor &v1, Traits::vertex_descriptor &v2, const double capacity_fwd, const double capacity_rev, Graph &g) {
	//check invalid node descriptor
	if (v1 == -1 || v2 == -1) {
		//Invalid. Do nothing
	} else {
		//	Check duplicated edge
		boost::property_map<Graph, boost::edge_reverse_t>::type rev = boost::get(boost::edge_reverse, g);
		if (check_duplicated_edge(func_list, v1, v2, g) == false && v1 != v2) {
			Traits::edge_descriptor e1 = add_edge(v1, v2, g).first;
			Traits::edge_descriptor e2 = add_edge(v2, v1, g).first;

			boost::put(boost::edge_capacity, g, e1, capacity_fwd);
			boost::put(boost::edge_capacity, g, e2, capacity_fwd);

			rev[e1] = e2;
			rev[e2] = e1;

			boost::property_map<Graph, visedge_type_t>::type g_evis = boost::get(visedge_type_t(), g);
			g_evis[e1] = true;
			g_evis[e2] = false;

			func_list->edge_list.insert(pair<int, int>(v1, v2));
		}
	}
}

Graph::vertex_descriptor add_default_vertex(Graph &g, sign_type_t su_type) {
	Graph::vertex_descriptor vtx = boost::add_vertex(g);

//	Set default property of the vertex
	boost::property_map<Graph, signed_unsigend_type_t>::type g_su = boost::get(signed_unsigend_type_t(), g);
	boost::property_map<Graph, visible_type_t>::type g_vi = boost::get(visible_type_t(), g);

	g_su[vtx] = su_type;
	g_vi[vtx] = true;
	return vtx;
}

void print_variable_list(func_vertex_ptr *func_list, int len) {
	int i, j;
	for (i = 0; i < len; i++) {
		printf("Function:%s\n", func_list[i]->func_name.c_str());
		for (j = 0; j < func_list[i]->variable_list.size(); j++) {
			printf("\t%s\n", func_list[i]->variable_list.at(j)->debug_info->var_name.c_str());
		}
	}
}

//Chech whether the operation represented by <op> already exist in operation list (vector)
bool check_duplicate_operation(func_vertex_ptr func_block, Operation *op) {
	if (func_block->op_list.count(op->exp) > 0) {
		return true;
	} else {
		return false;
	}
}

int search_by_func_name(func_vertex_ptr func_block, fblock_ptr *vine_ir_block) {
	int result = -1;
	int i;

	for (i = 0; i < cfg_funclist_length; i++) {
		if (func_block->func_name == vine_ir_block[i]->func->name) {
			result = i;
			break;
		}
	}
	return result;

}

/*Tell me whether v_des is a node of variable by traveling through variable vector*/bool is_var(func_vertex_ptr func_block, Graph::vertex_descriptor v_des) {
	bool res = false;
	int i;
	for (i = 0; i < func_block->variable_list.size(); i++) {
		if (func_block->variable_list.at(i)->my_descriptor == v_des) {
			res = true;
			break;
		}
	}
	return res;
}

//Find correlated variable node of a MEM exp, and return descriptor
//Return -1 if there is no such a descriptor.
int var_lookup(func_vertex_ptr func_block, Exp *exp, int block, int stmt) {
	int result = -1;
	int i, j;
	exp_type_t exp_type = exp->exp_type;
	switch (exp_type) {
	case MEM: {
		switch (((Mem *) exp)->addr->exp_type) {
		case CONSTANT: {
			//////////////////////////////////
			//un-handle!!!!!!!!!!!!!!!!!!!!!!
			break;
		}
		case BINOP: {
			for (i = 0; i < func_block->variable_list.size(); i++) {
				dvariable *dvar = func_block->variable_list.at(i)->debug_info;
				if (dvar->cmp_loc(((Mem *) exp)->addr, func_block->stmt_block->block_list[block]->block[stmt]->asm_address) == true) {
					result = func_block->variable_list.at(i)->my_descriptor;
					break;
				}
			}

			break;
		}
		case TEMP: {
			Tmp_s *addr = ((Tmp_s *) ((Mem *) exp)->addr);
			for (i = 0; i < func_block->variable_list.size(); i++) {
				for (j = 0; j < func_block->variable_list.at(i)->field_copy_list.size(); j++) {
					if (func_block->variable_list.at(i)->field_copy_list.at(j)->cmp_tmp(addr) == true) {
						result = result = func_block->variable_list.at(i)->my_descriptor;
						break;
					}
				}
			}
			break;
		}
		default: {
			break;
		}
		};
		break;
	}

	default: {
		break;
	}
	}

	return result;
}

//Return whether reg_tmp is a flag register
bool is_flag(Tmp_s *reg_tmp) {
	bool res = false;
	int i;
	if (reg_tmp->name == str_reg[EFLAGS]) {
		res = true;
	} else {
		for (i = R_CF; i <= R_ACFLAG; i++) {
			if (reg_tmp->name == str_reg[i]) {
				res = true;
				break;
			}
		}
	}
	return res;
}

bool push_register(func_vertex_ptr func_block, Tmp_s *reg_tmp, Graph& g) {
//	Search register corresponding to certain expression
//	If cannot find, push into vector, and return true
//	otherwise return vector directly

	//Don't add flag
	if (is_flag(reg_tmp) == false) {
		if (func_block->reg_list.count(reg_tmp->index) > 0) {
			return true;
		} else {
			//register not exist
			//push new register into vector
			boost::property_map<Graph, id_index_type_t>::type g_id = boost::get(id_index_type_t(), g);
			boost::property_map<Graph, id_exp_type_t>::type g_exp = boost::get(id_exp_type_t(), g);
			boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
			boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

			//Graph::vertex_descriptor v_reg = boost::add_vertex(g);
			Graph::vertex_descriptor v_reg = add_default_vertex(g, UNSIGNED_T);
			Register *reg = new Register(reg_tmp, v_reg);
			func_block->reg_list.insert(pair<int, Register *>(reg_tmp->index, reg));
			g_id[v_reg] = reg_tmp->index;
			g_vet[v_reg] = REGISTER;
			g_name[v_reg] = reg_tmp->tostring();
			return true;
		}
	}

	return false;
}

//Looking for a reg node that identical to target
//and return its position in reg node list (vector)
bool search_reg(func_vertex_ptr func_list, Tmp_s *target) {
	if (func_list->reg_list.count(target->index) >= 0) {
		return true;
	} else {
		return false;
	}
}

int search_var(func_vertex_ptr func_list, int block, int stmt, Mem *target) {
	int result = -1;
	int i;

	int buf = var_lookup(func_list, target, block, stmt);
	//printf("var lookup: %d\n",buf);
	if (buf != -1) {
		for (i = 0; i < func_list->variable_list.size(); i++) {
			if (func_list->variable_list.at(i)->my_descriptor == buf) {
				result = i;
				break;
			}
		}
	}

	return result;
}

//Return the descriptor of node
Graph::vertex_descriptor node_searcher(func_vertex_ptr func_list, int block, int stmt, Exp *target) {
	Graph::vertex_descriptor result = -1;
	int res = -1;

	if (target->exp_type == TEMP) {
		if (search_reg(func_list, (Tmp_s *) target) == true) {
			result = func_list->reg_list.at(((Tmp_s *) target)->index)->my_descriptor;
		}
	} else if (target->exp_type == MEM) {
		res = search_var(func_list, block, stmt, (Mem *) target);
		if (res != -1) {
			result = func_list->variable_list.at(res)->my_descriptor;
		}
	}

	return result;
}

//Looking for the defination of target starting from the given position
//return the Exp * of the exp equaling to target
bool def_searcher(fblock_ptr vine_ir_block, int block_no, int stmt_no, int *block, int *stmt, Tmp_s *target, Exp *&res) {
	/*No defination for Tmp_s whose index is from 0 to 35*/
	if (target->index <= REGMAX) {
		return false;
	}

	int i, j;
	bool result = false;
	for (i = block_no; i > 0; i--) {
		for (j = (i == block_no ? stmt_no : (vine_ir_block->block_list[i]->blen - 1)); j > 0; j--) {
			if (vine_ir_block->block_list[i]->block[j]->stmt_type == MOVE) {
				if (((Move *) vine_ir_block->block_list[i]->block[j])->lhs->exp_type == TEMP) {
					if (get_reg_position(((Temp *) ((Move *) vine_ir_block->block_list[i]->block[j])->lhs)->name) != -1) {
						if (((Tmp_s *) (Temp *) ((Move *) vine_ir_block->block_list[i]->block[j])->lhs)->index == target->index
						//||((Tmp_s *)(Temp *)((Move *)vine_ir_block->block_list[i]->block[j])->lhs)->name == target->name
								) {
							res = ((Move *) vine_ir_block->block_list[i]->block[j])->rhs;
							if (block != 0) {
								*block = i;
							}
							if (stmt != 0) {
								*stmt = j;
							}
							result = true;
							return result;
						}
					}
				}
			}
		}
	}

	return result;
}

/*Look for the defination of SF*/
/*Return the corresponding nodes of var/reg/exp in the equation of SF*/bool sf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g) {
	Exp *def;
	bool result = false;
	Graph::vertex_descriptor opr_l = -1;
	Graph::vertex_descriptor opr_r = -1;
	if (get_reg_position(exp->name) == -1) {
		return result;
	} else {
		int current_block, current_stmt;
		if (def_searcher(vine_ir_block, block_no, stmt_no, &current_block, &current_stmt, ((Tmp_s *) exp), def) == false) {
			return result;
		} else {
			//Now the defination of SF is in def
			//Get the Exp = a + b
			//printf("def: %x\n",def);
			Exp *tmp = def;
			//printf("sf_handler: %s\n",tmp->tostring().c_str());
			while (tmp->exp_type == BINOP) {
				if (((BinOp *) tmp)->binop_type == MINUS) {
					//tmp = a + b
					result = true;
					break;
				} else {
					if ((((BinOp *) tmp)->lhs->exp_type == BINOP && ((BinOp *) tmp)->rhs->exp_type == BINOP) || (((BinOp *) tmp)->lhs->exp_type != BINOP && ((BinOp *) tmp)->rhs->exp_type != BINOP)) {
						result = false;
						return result;
					} else if (((BinOp *) tmp)->lhs->exp_type == BINOP && ((BinOp *) tmp)->rhs->exp_type != BINOP) {
						tmp = ((BinOp *) tmp)->lhs;
						//break;
					} else if (((BinOp *) tmp)->rhs->exp_type == BINOP && ((BinOp *) tmp)->lhs->exp_type != BINOP) {
						tmp = ((BinOp *) tmp)->rhs;
						//break;
					}
				}
			}

			//Now tmp = a + b
			//Lookup a and b in graph, and connect them to signed node
			//printf("tmp: %s\n",tmp->tostring().c_str());
			if (((BinOp *) tmp)->lhs != 0) {
				opr_l = node_searcher(func_list, block_no, stmt_no, ((BinOp *) tmp)->lhs);
				if (opr_l != -1) {
					add_edge_with_cap(func_list, func_list->s_des, opr_l, MAX_CAP, 0, g);
				}
			}
			if (((BinOp *) tmp)->rhs != 0) {
				opr_r = node_searcher(func_list, block_no, stmt_no, ((BinOp *) tmp)->rhs);
				if (opr_r != -1) {
					add_edge_with_cap(func_list, func_list->s_des, opr_r, MAX_CAP, 0, g);
				}
			}
		}
	}

	return result;
}

//Similar to sf_handler except:
//1. CF = a<b
//2. unsigned
bool cf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g) {
	Exp *def;
	bool result = false;
	Graph::vertex_descriptor opr_l = -1;
	Graph::vertex_descriptor opr_r = -1;
	if (get_reg_position(exp->name) == -1) {
		return result;
	} else {
		int current_block, current_stmt;
		if (def_searcher(vine_ir_block, block_no, stmt_no, &current_block, &current_stmt, ((Tmp_s *) exp), def) == false) {
			return result;
		} else {
			//Now the defination of CF is in def
			//Get the Exp = a < b
			Exp *tmp = def;
			printf("cf_handler: %s\n", tmp->tostring().c_str());
			while (tmp->exp_type == BINOP) {
				if (((BinOp *) tmp)->binop_type == LT) {
					//tmp = a < b
					result = true;
					break;
				} else {
					if ((((BinOp *) tmp)->lhs->exp_type == BINOP && ((BinOp *) tmp)->rhs->exp_type == BINOP) || (((BinOp *) tmp)->lhs->exp_type != BINOP && ((BinOp *) tmp)->rhs->exp_type != BINOP)) {
						result = false;
						return result;
					} else if (((BinOp *) tmp)->lhs->exp_type == BINOP && ((BinOp *) tmp)->rhs->exp_type != BINOP) {
						tmp = ((BinOp *) tmp)->lhs;
						//break;
					} else if (((BinOp *) tmp)->rhs->exp_type == BINOP && ((BinOp *) tmp)->lhs->exp_type != BINOP) {
						tmp = ((BinOp *) tmp)->rhs;
						//break;
					}
				}
			}

			//Now tmp = a + b
			//Lookup a and b in graph, and connect them to unsigned node
			if (((BinOp *) tmp)->lhs != 0) {
				opr_l = node_searcher(func_list, block_no, stmt_no, ((BinOp *) tmp)->lhs);
				if (opr_l != -1) {
					add_edge_with_cap(func_list, opr_l, func_list->u_des, MAX_CAP, 0, g);
				}
			}
			if (((BinOp *) tmp)->rhs != 0) {
				opr_r = node_searcher(func_list, block_no, stmt_no, ((BinOp *) tmp)->rhs);
				if (opr_r != -1) {
					add_edge_with_cap(func_list, opr_r, func_list->u_des, MAX_CAP, 0, g);
				}
			}
		}
	}

	return result;
}

//Handle the 2 operands of smod.
//var/register connect to signed node
//operand_binop and operand_var are descriptors
void smod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var, Graph& g) {
	//Handle bin_op
	boost::property_map<Graph, id_exp_type_t>::type g_exp = boost::get(id_exp_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	if (func_block->op_list.at(g_exp[operand_binop])->op_type == BIN_OP) {
		if (((Bin_Operation *) func_block->op_list.at(g_exp[operand_binop]))->binop_type == BITOR) {
			Graph::vertex_descriptor opr_l = ((Bin_Operation *) func_block->op_list.at(g_exp[operand_binop]))->operand_l;
			Graph::vertex_descriptor opr_r = ((Bin_Operation *) func_block->op_list.at(g_exp[operand_binop]))->operand_r;
			if (g_vet[opr_l] == OPERATION && (g_vet[opr_r] == REGISTER || g_vet[opr_r] == VARIABLE)) {
				cout << "set " << g_name[opr_l] << " to sigend (%$)" << endl;
				add_edge_with_cap(func_block, func_block->s_des, opr_r, MAX_CAP, 0, g);
			} else if (g_vet[opr_r] == OPERATION && (g_vet[opr_l] == REGISTER || g_vet[opr_l] == VARIABLE)) {
				cout << "set " << g_name[opr_r] << " to sigend (%$)" << endl;
				add_edge_with_cap(func_block, func_block->s_des, opr_l, MAX_CAP, 0, g);
			}

		}
	}

	//Handle var/register
	add_edge_with_cap(func_block, func_block->s_des, operand_var, MAX_CAP, 0, g);
}

void handle_smod(func_vertex_ptr func_block, int descriptor, Graph& g) {
	boost::property_map<Graph, id_exp_type_t>::type g_id = boost::get(id_exp_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	if (func_block->op_list.at(g_id[descriptor])->op_type == BIN_OP) {
		if (((Bin_Operation *) func_block->op_list.at(g_id[descriptor]))->binop_type == SMOD) {
			int op_l = ((Bin_Operation *) func_block->op_list.at(g_id[descriptor]))->operand_l;
			int op_r = ((Bin_Operation *) func_block->op_list.at(g_id[descriptor]))->operand_r;
			if (op_l != -1 && op_r != -1) {
				if (g_vet[op_l] == OPERATION && (g_vet[op_r] == VARIABLE || g_vet[op_r] == REGISTER)) {
					if (func_block->op_list.at(g_id[op_l])->op_type == BIN_OP) {
						smod_operand_handler(func_block, op_l, op_r, g);
					}
				} else if (g_vet[op_r] == OPERATION && (g_vet[op_l] == VARIABLE || g_vet[op_l] == REGISTER)) {
					if (func_block->op_list.at(g_id[op_r])->op_type == BIN_OP) {
						smod_operand_handler(func_block, op_r, op_l, g);
					}
				}
			}
		}
	}
}

//Handle the 2 operands of smod.
//var/register connect to signed node
//operand_binop and operand_var are descriptors
void mod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var, Graph& g) {
	//Handle bin_op
	boost::property_map<Graph, id_exp_type_t>::type g_id = boost::get(id_exp_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	if (func_block->op_list.at(g_id[operand_binop])->op_type == BIN_OP) {
		if (((Bin_Operation *) func_block->op_list.at(g_id[operand_binop]))->binop_type == BITOR) {
			Graph::vertex_descriptor opr_l = ((Bin_Operation *) func_block->op_list.at(g_id[operand_binop]))->operand_l;
			Graph::vertex_descriptor opr_r = ((Bin_Operation *) func_block->op_list.at(g_id[operand_binop]))->operand_r;
			//printf("left:%s\tright:%s\n",g_name[opr_l].c_str(),g_name[opr_r].c_str());
			if (g_vet[opr_l] == OPERATION && (g_vet[opr_r] == REGISTER || g_vet[opr_r] == VARIABLE)) {
				add_edge_with_cap(func_block, opr_r, func_block->u_des, MAX_CAP, 0, g);
				cout << "set " << g_name[opr_r] << " to unsigend (%)" << endl;
				//printf("Add edge\n");
			} else if (g_vet[opr_r] == OPERATION && (g_vet[opr_l] == REGISTER || g_vet[opr_l] == VARIABLE)) {
				add_edge_with_cap(func_block, opr_l, func_block->u_des, MAX_CAP, 0, g);
				cout << "set " << g_name[opr_l] << " to unsigend (%)" << endl;
				//printf("Add edge\n");
			} else {
				//printf("Not a valid %\n");
			}

		}
	}

	//Handle var/register
	add_edge_with_cap(func_block, operand_var, func_block->u_des, MAX_CAP, 0, g);
}

//descriptor is the descriptor of % operation
void handle_mod(func_vertex_ptr func_block, int descriptor, Graph& g) {
	boost::property_map<Graph, id_exp_type_t>::type g_id = boost::get(id_exp_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	if (func_block->op_list.at(g_id[descriptor])->op_type == BIN_OP) {
		if (((Bin_Operation *) func_block->op_list.at(g_id[descriptor]))->binop_type == MOD) {
			int op_l = ((Bin_Operation *) func_block->op_list.at(g_id[descriptor]))->operand_l;
			int op_r = ((Bin_Operation *) func_block->op_list.at(g_id[descriptor]))->operand_r;
			if (op_l != -1 && op_r != -1) {
				if (g_vet[op_l] == OPERATION && (g_vet[op_r] == VARIABLE || g_vet[op_r] == REGISTER)) {
					if (func_block->op_list.at(g_id[op_l])->op_type == BIN_OP) {
						mod_operand_handler(func_block, op_l, op_r, g);
					}
				} else if (g_vet[op_r] == OPERATION && (g_vet[op_l] == VARIABLE || g_vet[op_l] == REGISTER)) {
					if (func_block->op_list.at(g_id[op_r])->op_type == BIN_OP) {
						mod_operand_handler(func_block, op_r, op_l, g);
					}
				}
			}
		}
	}
}

void handle_sar(func_vertex_ptr func_block, int descriptor, Graph& g) {
	boost::property_map<Graph, id_pos_type_t>::type g_id = boost::get(id_pos_type_t(), g);
	boost::property_map<Graph, id_exp_type_t>::type g_exp = boost::get(id_exp_type_t(), g);
	boost::property_map<Graph, id_index_type_t>::type g_index = boost::get(id_index_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	if (func_block->op_list.at(g_exp[descriptor])->op_type == BIN_OP) {
		if (((Bin_Operation *) func_block->op_list.at(g_exp[descriptor]))->binop_type == ARSHIFT) {
			Graph::vertex_descriptor op_l = ((Bin_Operation *) func_block->op_list.at(g_exp[descriptor]))->operand_l;
			if (op_l != -1) {
				if (g_vet[op_l] == VARIABLE) {
					if (func_block->variable_list.at(g_id[op_l])->debug_info->var_length == 4) {
						add_edge_with_cap(func_block, func_block->s_des, op_l, MAX_CAP, 0, g);
						cout << "set " << g_name[op_l] << " to sigend ($>>)" << endl;
					}
				} else if (g_vet[op_l] == REGISTER) {
					if (func_block->reg_list.at(g_index[op_l])->exp->exp_type == TEMP) {
						if (((Temp *) func_block->reg_list.at(g_index[op_l])->exp)->typ == REG_32) {
							add_edge_with_cap(func_block, func_block->s_des, op_l, MAX_CAP, 0, g);
							cout << "set " << g_name[op_l] << " to sigend ($>>)" << endl;
						}
					}
				} else if (g_vet[op_l] == OPERATION) {
					//!!!!!!!
					//How to handle Exp?
					//add_edge_with_cap(func_block->s_des, op_l, rev, MAX_CAP, 0, g);
				}
			}
		}
	}
}

void handle_shr(func_vertex_ptr func_block, int descriptor, Graph& g) {
	boost::property_map<Graph, id_index_type_t>::type g_index = boost::get(id_index_type_t(), g);
	boost::property_map<Graph, id_exp_type_t>::type g_exp = boost::get(id_exp_type_t(), g);
	boost::property_map<Graph, id_pos_type_t>::type g_id = boost::get(id_pos_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	/*Test whether its a shr in flag computing*/
	/*If so, don't handle it.*/
	int stmt, block;
	stmt = func_block->op_list.at(g_exp[descriptor])->stmt_number;
	block = func_block->op_list.at(g_exp[descriptor])->block_number;
	Stmt *tmp = func_block->stmt_block->block_list[block]->block[stmt];
	if (tmp->stmt_type == MOVE) {
		Move *tmp_mv = (Move *) tmp;
		if (is_tmps(tmp_mv->lhs) == true) {
			Tmp_s * tmps = (Tmp_s *) tmp_mv->lhs;
			if (is_flag(tmps)) {
				return;
			}
		}
	}

	if (func_block->op_list.at(g_exp[descriptor])->op_type == BIN_OP) {
		if (((Bin_Operation *) func_block->op_list.at(g_exp[descriptor]))->binop_type == RSHIFT) {
			Graph::vertex_descriptor op_l = ((Bin_Operation *) func_block->op_list.at(g_exp[descriptor]))->operand_l;
			if (op_l != -1) {
				if (g_vet[op_l] == VARIABLE) {
					if (func_block->variable_list.at(g_id[op_l])->debug_info->var_length == 4) {
						add_edge_with_cap(func_block, op_l, func_block->u_des, MAX_CAP, 0, g);
						cout << "set " << g_name[op_l] << "to unsigend (>>)" << endl;
					}
				} else if (g_vet[op_l] == REGISTER) {
					if (func_block->reg_list.at(g_index[op_l])->exp->exp_type == TEMP) {
						if (((Temp *) func_block->reg_list.at(g_index[op_l])->exp)->typ == REG_32) {
							add_edge_with_cap(func_block, op_l, func_block->u_des, MAX_CAP, 0, g);
							cout << "set " << g_name[op_l] << "to unsigend (>>)" << endl;
						}
					}
				} else if (g_vet[op_l] == OPERATION) {
					//!!!!!!!
					//How to handle Exp?
					//add_edge_with_cap(op_l, func_block->u_des, rev, MAX_CAP, 0, g);
				}
			}
		}
	}
}

void handle_operation(func_vertex_ptr func_block, Graph& g) {
	boost::property_map<Graph, id_exp_type_t>::type g_id = boost::get(id_exp_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	pair<vertex_iter, vertex_iter> vp;
	for (vp = vertices(g); vp.first != vp.second; ++vp.first) {
		if (g_vet[*vp.first] == OPERATION) {
			Exp *node_id = g_id[*vp.first];
			if (func_block->op_list.at(node_id)->op_type == BIN_OP) {
				switch (((Bin_Operation *) func_block->op_list.at(node_id))->binop_type) {
				case SMOD: {
					//printf("handle smod\n");
					handle_smod(func_block, *vp.first, g);
					break;
				}
				case MOD: {
					//printf("handle mod\n");
					handle_mod(func_block, *vp.first, g);
					break;
				}
				case ARSHIFT: {
					//printf("handle arshift\n");
					handle_sar(func_block, *vp.first, g);
					break;
				}
				case RSHIFT: {
					//printf("handle rshift\n");
					handle_shr(func_block, *vp.first, g);
					break;
				}
				default:
					break;
				}
			}
		}
	}
}

void check_cjmp(fblock_ptr vine_ir_block, func_vertex_ptr func_list, Exp *cond, int block_no, int stmt_no, Graph& g) {
//	Look for <, <=, >, >= and add edges to signed/unsigend node
//	cond is the condition of the cjmp
	Exp *tmp = cond;
	while (tmp->exp_type == CAST) {
		tmp = ((Cast *) tmp)->exp;
	}

//	Now tmp is a binOp or unOp
	switch (tmp->exp_type) {
	case BINOP: {
		switch (((BinOp *) tmp)->binop_type) {
		case BITOR: {
			if (((BinOp *) tmp)->rhs->exp_type == TEMP) {
				if (((Temp *) ((BinOp *) tmp)->rhs)->name == str_reg[R_ZF]) {
					if (((BinOp *) tmp)->lhs->exp_type == BINOP) {
						if (((BinOp *) ((BinOp *) tmp)->lhs)->binop_type == XOR) {
							if (((BinOp *) ((BinOp *) tmp)->lhs)->lhs->exp_type == TEMP || ((BinOp *) ((BinOp *) tmp)->lhs)->rhs->exp_type == TEMP) {
								if (((Temp *) ((BinOp *) ((BinOp *) tmp)->lhs)->lhs)->name == str_reg[R_SF] || ((Temp *) ((BinOp *) ((BinOp *) tmp)->lhs)->rhs)->name == str_reg[R_OF]) {
									//SF^OF | ZF
									//jle or jg
									sf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *) ((BinOp *) ((BinOp *) tmp)->lhs)->lhs, g);
								}
							}
						}
					} else if (((BinOp *) tmp)->lhs->exp_type == TEMP) {
						if (((Temp *) ((BinOp *) tmp)->lhs)->name == str_reg[R_CF]) {
							//CF | ZF
							//jbe or ja
							cf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *) ((BinOp *) tmp)->lhs, g);
						}
					}
				}
			}
			break;
		}
		case XOR: {
			if (((BinOp *) tmp)->lhs->exp_type == TEMP || ((BinOp *) tmp)->rhs->exp_type == TEMP) {
				if (((Temp *) ((BinOp *) tmp)->lhs)->name == str_reg[R_SF] || ((Temp *) ((BinOp *) tmp)->rhs)->name == str_reg[R_OF]) {
					//SF^OF
					//jl or jge
					sf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *) ((BinOp *) tmp)->lhs, g);
				}
			}
			break;
		}
		default:
			break;
		}
		break;
	}
	case TEMP: {
		//CF
		if (((Temp *) tmp)->name == str_reg[R_CF]) {
			//jae or jb
			cf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *) tmp, g);
		}
		break;
	}
	default:
		break;
	}
}

bool compare_mem(Mem *former, Mem *latter) {
	//Check whether the 2 Mem* represent the same location
	bool result = false;
	if (former->addr->exp_type != latter->addr->exp_type) {
		result = false;
	} else {
		if (former->addr->exp_type == BINOP) {
			if (((BinOp *) former->addr)->lhs->exp_type == TEMP && ((BinOp *) former->addr)->rhs->exp_type == CONSTANT && ((BinOp *) latter->addr)->lhs->exp_type == TEMP && ((BinOp *) latter->addr)->rhs->exp_type == CONSTANT) {
				if (((Tmp_s *) ((BinOp *) former->addr)->lhs)->index == ((Tmp_s *) ((BinOp *) latter->addr)->lhs)->index && ((Constant *) ((BinOp *) former->addr)->rhs)->val == ((Constant *) ((BinOp *) latter->addr)->rhs)->val) {
					result = true;
				}
			}
		} else if (former->addr->exp_type == TEMP) {
			if (get_reg_position(((Temp *) former->addr)->name) != -1 && get_reg_position(((Temp *) latter->addr)->name) != -1) {
				if (((Tmp_s *) former->addr)->index == ((Tmp_s *) latter->addr)->index) {
					result = true;
				}
			}
		}
	}
	return result;
}

//Compare 2 Exp* that return -1 as descriptor, include:
//1-mem[] whose corresponding variable node
//2-constant, which is not included in graph by default
//3-?????
bool compare_exp(Exp *former, Exp *latter) {
	bool result = false;
	if (former->exp_type != latter->exp_type) {
		return result;
	} else {
		exp_type_t type = former->exp_type;
		switch (type) {
		case MEM: {
			result = compare_mem((Mem *) former, (Mem *) latter);
			break;
		}
		case CONSTANT: {
			if (((Constant *) former)->val == ((Constant *) latter)->val) {
				result = true;
			}
			break;
		}
		case TEMP:{
			if(is_tmps(former) == false){
				return false;
			}else{
				if(((Tmp_s *)former)->index == ((Tmp_s *)latter)->index){
					return true;
				}else{
					return false;
				}
			}
			break;
		}
		default: {
			break;
		}
		}
	}
	return result;
}

//Return s/u type by reading a Dwarf_Unsigned
sign_type_t get_su_type(Dwarf_Unsigned su_type) {
	sign_type_t result = UNKNOW_T;
	if (su_type == DW_ATE_unsigned || su_type == DW_ATE_unsigned_char) {
		result = UNSIGNED_T;
	} else if (su_type == DW_ATE_signed || su_type == DW_ATE_signed_char) {
		result = SIGNED_T;
	}

	return result;
}

//function: get the full name of a base variable recursively
string get_full_name(dbase *var) {
	dvariable *tmp = var;
	string result = var->var_name;
	tmp = tmp->parent;
	while (tmp != 0) {
		switch (tmp->var_struct_type) {
		case DVAR_POINTER: {
			if (tmp->parent == 0) {
				result = "*" + result;
			} else {
				result = "->" + result;
			}
			break;
		}
		case DVAR_STRUCT: {
			if (tmp->parent != 0) {
				if (tmp->parent->var_struct_type == DVAR_ARRAY) {
					break;
				} else {
					result = tmp->var_name + "." + result;
				}
			} else {
				result = tmp->var_name + "." + result;
			}
			break;
		}
		case DVAR_BASE: {
			break;
		}
		default: {
			break;
		}
		}

		tmp = tmp->parent;
	}
	//tcout<<"get_full_name: "<<result<<endl;
	return result;
}

//check whether it is a movzbl/movsbl
//set source variable to signed/unsigned, respectively
void check_movzsbl(func_vertex_ptr func_list, int block, int stmt, Cast *src, Tmp_s *dst, Graph::vertex_descriptor v_src, Graph &g) {
	reg_t typ = REG_32;
	switch(src->exp->exp_type){
	case MEM:{
		typ = ((Mem *) src->exp)->typ;
		break;
	}
	case CAST:{
		typ = ((Cast *) src->exp)->typ;
		break;
	}
	default:
		break;
	}

	if (typ < dst->typ) {
		if (src->cast_type == CAST_SIGNED) {
			//movsbl -> signed
			add_edge_with_cap(func_list, func_list->s_des, v_src, MAX_CAP, 0, g);
		} else if (src->cast_type == CAST_UNSIGNED) {
			//movzbl -> unsigned

			/*look for movsbl in next block*/
			if ((block + 1) < func_list->stmt_block->len) {
				for (int i = 0; i < func_list->stmt_block->block_list[block + 1]->blen; i++) {
					Stmt *exp = func_list->stmt_block->block_list[block + 1]->block[i];
					if (exp->stmt_type != MOVE) {
						continue;
					}
					if (((Move *) exp)->rhs->exp_type != CAST) {
						continue;
					}
					Cast *cast = ((Cast *) ((Move *) exp)->rhs);
					if(cast->cast_type == CAST_SIGNED){
						return;
					}
				}
			}

			/*check whether it's cast to a condition*/
			int current_block = block;
			int current_stmt = stmt;
			BinOp *bop;
			Move *move;
			Exp *exp;
			bool result = get_next_stmt(func_list->stmt_block, current_block, current_stmt, &current_block, &current_stmt);
			while (result != false) {
				if (func_list->stmt_block->block_list[current_block]->block[current_stmt]->stmt_type != MOVE) {
					goto next_stmt;
				}
				move = ((Move *) func_list->stmt_block->block_list[current_block]->block[current_stmt]);
				if(is_tmps(move->lhs) == false){
					goto next_stmt;
				}
				if(((Tmp_s *)move->lhs)->name != str_reg[R_ZF]){
					goto next_stmt;
				}
				if(move->rhs->exp_type != BINOP){
					break;
				}
				bop = (BinOp *)move->rhs;
				if(bop->lhs->exp_type != CAST ||
						((Cast *)bop->lhs)->exp->exp_type != CAST){
					break;
				}
				exp = ((Cast *)((Cast *)bop->lhs)->exp)->exp;
				cout<<"[movzsbl]"<<exp->tostring()<<endl;
				cout<<"[movzsbl]"<<dst->tostring()<<endl;
				if(compare_exp(exp, dst) == true){
					return;
				}else{
					break;
				}

				next_stmt:
				result = get_next_stmt(func_list->stmt_block, current_block, current_stmt, &current_block, &current_stmt);
			}

			add_edge_with_cap(func_list, v_src, func_list->u_des, MAX_CAP, 0, g);
		} else {
			//neither
			//do nothing
		}
	}

}

//Set signed/unsigned of function params and return value according to function name
//Use dbg info or harded coded assignment based on existed knowledge
void check_call(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block, int stmt, string func_name, Graph &g) {
	int i;
	int res = -1;
	for (i = IFUNC_STRCAT; i <= IFUNC_WMEMCMP; i++) {
		if (func_name == indirect[i]) {
			res = i;
			break;
		}
	}

	if (res == -1) {
		check_func(vine_ir_block, func_list, block, stmt, func_name, g);
	} else {
		//indirect function
		//set func_name to a hardcoded special function name, who has the same ret/param types of the original function
		bool result;
		int current_block = 0;
		int current_stmt = 0;
		Exp *ret;

		switch (res) {
		case IFUNC_STRCAT: {
			check_func(vine_ir_block, func_list, block, stmt, "__strcat_g", g);
			break;
		}
		case IFUNC_INDEX: {
			check_func(vine_ir_block, func_list, block, stmt, "__strchr_g", g);
			break;
		}
		case IFUNC_STRCMP: {
			check_func(vine_ir_block, func_list, block, stmt, "__strcmp_gg", g);
			break;
		}
		case IFUNC_STRCPY: {
			check_func(vine_ir_block, func_list, block, stmt, "__strcpy_g", g);
			break;
		}
		case IFUNC_STRRCHR: {
			check_func(vine_ir_block, func_list, block, stmt, "__strrchr_g", g);
			break;
		}
		case IFUNC_STRCSPN: {
			check_func(vine_ir_block, func_list, block, stmt, "__strcspn_g", g);
			break;
		}
		case IFUNC_STRLEN: {
			check_func(vine_ir_block, func_list, block, stmt, "__strlen_g", g);
			break;
		}
		case IFUNC_STRNLEN: {
			check_func(vine_ir_block, func_list, block, stmt, "__strnlen_ia32", g);
			break;
		}
		case IFUNC_STRNCAT: {
			check_func(vine_ir_block, func_list, block, stmt, "__strncat_g", g);
			break;
		}
		case IFUNC_STRNCMP: {
			check_func(vine_ir_block, func_list, block, stmt, "__strncmp_g", g);
			break;
		}
		case IFUNC_STRNCPY: {
			check_func(vine_ir_block, func_list, block, stmt, "__strncpy_gg", g);
			break;
		}
		case IFUNC_RINDEX: {
			check_func(vine_ir_block, func_list, block, stmt, "__strrchr_g", g);
			break;
		}
		case IFUNC_STRPBRK: {
			check_func(vine_ir_block, func_list, block, stmt, "__strpbrk_g", g);
			break;
		}
		case IFUNC_STRSPN: {
			check_func(vine_ir_block, func_list, block, stmt, "__strspn_g", g);
			break;
		}
		case IFUNC_MEMCHR: {
			//use memset() instead
			check_func(vine_ir_block, func_list, block, stmt, "__memset_gcn_by4", g);
			break;
		}
		case IFUNC_BCMP: {
			//int bcmp(const void *s1, const void *s2, size_t n)
			result = get_return_value(vine_ir_block, block, stmt, &current_block, &current_stmt, ret);
			if (result == true) {
				set_single_edge(func_list, ret, current_block, current_stmt, SIGNED_T, g);
			}

			result = get_xth_param(vine_ir_block, 8, block, stmt, &current_block, &current_stmt, ret);
			if (result == true) {
				set_single_edge(func_list, ret, current_block, current_stmt, UNSIGNED_T, g);
			}
			break;
		}
		case IFUNC_MEMMOVE: {
			//void *memmove(void *dest, const void *src, size_t n)
			result = get_xth_param(vine_ir_block, 8, block, stmt, &current_block, &current_stmt, ret);
			if (result == true) {
				set_single_edge(func_list, ret, current_block, current_stmt, UNSIGNED_T, g);
			}
			break;
		}
		case IFUNC_MEMSET: {
			check_func(vine_ir_block, func_list, block, stmt, "__memset_gcn_by4", g);
			break;
		}
		case IFUNC_MEMPCPY: {
			//mempcpy's type in string.h is different from that in man doc
			//mempcpy has the same type as memcpy
			check_func(vine_ir_block, func_list, block, stmt, "__memcpy_g", g);
			break;
		}
		case IFUNC_BCOPY: {
			//void bcopy(const void *src, void *dest, size_t n)
			result = get_xth_param(vine_ir_block, 8, block, stmt, &current_block, &current_stmt, ret);
			if (result == true) {
				set_single_edge(func_list, ret, current_block, current_stmt, UNSIGNED_T, g);
			}
			break;
		}
		case IFUNC_BZERO: {
			//void bzero(void *s, size_t n)
			result = get_xth_param(vine_ir_block, 4, block, stmt, &current_block, &current_stmt, ret);
			if (result == true) {
				set_single_edge(func_list, ret, current_block, current_stmt, UNSIGNED_T, g);
			}
			break;
		}
		case IFUNC_STPCPY: {
			check_func(vine_ir_block, func_list, block, stmt, "__stpcpy_g", g);
			break;
		}
		case IFUNC_STPNCPY: {
			//same param/ret type as strncpy
			check_func(vine_ir_block, func_list, block, stmt, "__strncpy_gg", g);
			break;
		}
		case IFUNC_STRCASECMP: {
			check_func(vine_ir_block, func_list, block, stmt, "__strcasecmp_nonascii", g);
			break;
		}
		case IFUNC_STRNCASECMP: {
			check_func(vine_ir_block, func_list, block, stmt, "__strcasecmp_l_nonascii", g);
			break;
		}
		case IFUNC_MEMCPY: {
			check_func(vine_ir_block, func_list, block, stmt, "__memcpy_g", g);
			break;
		}
		case IFUNC_RAWMEMCHR: {
			//use memset() instead
			check_func(vine_ir_block, func_list, block, stmt, "__memset_gcn_by4", g);
			break;
		}
		case IFUNC_MEMRCHR: {
			check_func(vine_ir_block, func_list, block, stmt, "__memrchr_ia32", g);
			break;
		}
		case IFUNC_STRSTR: {
			check_func(vine_ir_block, func_list, block, stmt, "__strstr_g", g);
			break;
		}
		case IFUNC_STRCASESTR: {
			check_func(vine_ir_block, func_list, block, stmt, "__strcasestr_ia32", g);
			break;
		}
		case IFUNC_WCSCHR: {
			check_func(vine_ir_block, func_list, block, stmt, "__wcschr_ia32", g);
			break;
		}
		case IFUNC_WCSCMP: {
			check_func(vine_ir_block, func_list, block, stmt, "__wcscmp_ia32", g);
			break;
		}
		case IFUNC_WCSCPY: {
			check_func(vine_ir_block, func_list, block, stmt, "__wcscpy_ia32", g);
			break;
		}
		case IFUNC_WCSLEN: {
			check_func(vine_ir_block, func_list, block, stmt, "__wcslen_ia32", g);
			break;
		}
		case IFUNC_WCSRCHR: {
			check_func(vine_ir_block, func_list, block, stmt, "__wcsrchr_ia32", g);
			break;
		}
		case IFUNC_WMEMCMP: {
			check_func(vine_ir_block, func_list, block, stmt, "__wmemcmp_ia32", g);
			break;
		}
		default: {
			break;
		}
		}
	}
}

//called by check_call()
//Handle each function by mapping its ret/param type to corresponding variables
//caller if set_edge()
void check_func(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block, int stmt, string func_name, Graph &g) {
	//No need to hardcode types
	//read dbg info and map types
	int res = -1;
	Dwarf_Die subprog;
	Dwarf_Debug dbg = 0;
	Dwarf_Error error;
	Dwarf_Handler errhand = 0;
	Dwarf_Ptr errarg = 0;
	bool result = false;
	int fd = open(DBGLIB, O_RDONLY);
	if (fd < 0) {
		printf("Failure attempting to open \"%s\"\n", DBGLIB);
	}
	res = dwarf_init(fd, DW_DLC_READ, errhand, errarg, &dbg, &error);
	if (res != DW_DLV_OK) {
		printf("Giving up, cannot do DWARF processing\n");
		exit(1);
	}
	result = libcdbg_read_cu(dbg, func_name, &subprog);
	if (result == true) {
		//DIE Getchu!
		int current_stmt = stmt;
		int current_block = block;

		//1 Check type of return value
		//get result exp

		Exp *ret_var = 0;

		result = get_return_value(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt, ret_var);

		if (result == false) {
			/*It may happen that the ret value is not used in this program*/
			/*e.g. fclose(fp)*/
		} else {
			/*set edge of ret value*/
			set_edge(vine_ir_block, func_list, dbg, subprog, current_block, current_stmt, NULL, ret_var, g);
		}

		//-------------------------------------------------------------------------------------------X
		//2 check type of each param
		Dwarf_Die param;
		int offset = 0;
		sign_type_t su_param;
		result = get_prev_stmt(vine_ir_block, block, stmt, &current_block, &current_stmt);

		res = dwarf_child(subprog, &param, &error);
		while (res == DW_DLV_OK) {
			//check tag = DW_TAG_formal_parameter
			Dwarf_Half child_tag;
			if (get_die_tag(param, &child_tag) != true) {
				//next child
			} else {
				if (child_tag != DW_TAG_formal_parameter) {
					//next child
				} else {
					while (result == true) {
						//get_prev_stmt() return false if reach the beginning of func
						//check whether param correspond to current stmt
						if (check_param(vine_ir_block->block_list[current_block]->block[current_stmt], offset) == true) {
							Exp *current_exp = ((Move *) vine_ir_block->block_list[current_block]->block[current_stmt])->rhs;
							set_edge(vine_ir_block, func_list, dbg, param, current_block, current_stmt, &offset, current_exp, g);
							break;
						} else {
							//go next
						}

						result = get_prev_stmt(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt);
					}
				}
			}
			res = dwarf_siblingof(dbg, param, &param, &error);
		}
	}

	//dealloc dbg
	res = dwarf_finish(dbg, &error);
	if (res != DW_DLV_OK) {
		perror("dwarf_finish failed in check_func!\n");
	}
}

//Set edges of a param/ret according to Die
bool set_edge(fblock_ptr vine_ir_block, func_vertex_ptr func_list, Dwarf_Debug dbg, Dwarf_Die param, int block, int stmt, int *new_offset, Exp *current_exp, Graph &g) {
	bool result;
	sign_type_t su_param;
	int length;
	//set s/u
	result = get_su(dbg, param, &su_param);
	if (result == false) {
		check_call_pointer(dbg, param, vine_ir_block, func_list, block, stmt, current_exp, g);
	} else {
		Graph::vertex_descriptor vtd = -1;
		vtd = read_exp(func_list, block, stmt, current_exp, g);
		if (vtd != -1) {
			if (su_param == SIGNED_T) {
				cout << current_exp->tostring() << "is signed because of libc info" << endl;
				add_edge_with_cap(func_list, func_list->s_des, vtd, MAX_CAP, 0, g);
			} else if (su_param == UNSIGNED_T) {
				cout << current_exp->tostring() << "is unsigned because of libc info" << endl;
				add_edge_with_cap(func_list, vtd, func_list->u_des, MAX_CAP, 0, g);
			} else {
				perror("UNKNOWN type parameter\n");
			}
		} else {
			perror("NO corresponding vertice for this exp\n");
			//FIXME: no corresponding vertice for this exp
			//Left not handled
		}
	}

	// update offset
	result = get_length(dbg, param, &length);
	if (result == false) {
		if (new_offset != 0) {
			char offstr[128];
			sprintf(offstr, "%d", *new_offset);
			string errmsg = "cannot get length of param at eps+" + std::string(offstr);
			perror(errmsg.c_str());
		} else {
			perror("cannot get length of ret value");
		}

		return false;
	}

	//new_offset is NULL if the caller send a ret value
	if (new_offset != 0) {
		*new_offset += length;
	}

	return true;
}

Graph::vertex_descriptor read_exp(func_vertex_ptr func_block, int block, int stmt, Exp *exp, Graph& g) {
	bool res;
	Graph::vertex_descriptor vtd = -1;
	if (func_block->node_list.count(exp) > 0) {
		return func_block->node_list.at(exp);
	}
	switch (exp->exp_type) {
	case BINOP: {
		//Don't add this operation to graph if both operands are constant
		if (((BinOp *) exp)->lhs->exp_type == CONSTANT && ((BinOp *) exp)->rhs->exp_type == CONSTANT) {
			break;
		}

		Graph::vertex_descriptor v_l;
		//= boost::add_vertex(g);
		Graph::vertex_descriptor v_r;
		Graph::vertex_descriptor v_op = -1;
		//= boost::add_vertex(g);
		v_l = read_exp(func_block, block, stmt, ((BinOp *) exp)->lhs, g);
		v_r = read_exp(func_block, block, stmt, ((BinOp *) exp)->rhs, g);

		Bin_Operation *op_vertex = new Bin_Operation(((BinOp *) exp)->binop_type, v_l, v_r, v_op, (BinOp *) exp, block, stmt);

		/*Check duplicate operation*/
		res = check_duplicate_operation(func_block, op_vertex);
		if (res == false) {
			//No duplicate
			boost::property_map<Graph, id_exp_type_t>::type g_exp = boost::get(id_exp_type_t(), g);
			boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
			boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

			//v_op= boost::add_vertex(g);
			v_op = add_default_vertex(g, UNSIGNED_T);
			op_vertex->my_descriptor = v_op;

			func_block->op_list.insert(pair<Exp *, Bin_Operation *>(exp, op_vertex));
			g_exp[v_op] = exp;
			g_vet[v_op] = OPERATION;

			char number[256];
			sprintf(number, "%d", v_op);
			string number_str = std::string(number);
			g_name[v_op] = number_str + ":" + binop_label[((BinOp *) exp)->binop_type];

			if (v_l != -1) {
				add_edge_with_cap(func_block, v_l, v_op, 1, 0, g);
			}
			if (v_r != -1) {
				add_edge_with_cap(func_block, v_r, v_op, 1, 0, g);
			}

			vtd = v_op;
		} else {
			//Duplicate.
			vtd = func_block->op_list.at(exp)->my_descriptor;
		}

		break;
	}
	case UNOP: {
		//Don't add this operation to graph if the operand is an constant
		if (((UnOp *) exp)->exp->exp_type == CONSTANT) {
			break;
		}

		Graph::vertex_descriptor v_target;
		Graph::vertex_descriptor v_op = -1;
		v_target = read_exp(func_block, block, stmt, ((UnOp *) exp)->exp, g);

		Un_Operation *op_vertex = new Un_Operation(((UnOp *) exp)->unop_type, v_target, v_op, (UnOp *) exp, block, stmt);

		res = check_duplicate_operation(func_block, op_vertex);
		if (res == false) {
			boost::property_map<Graph, id_exp_type_t>::type g_exp = boost::get(id_exp_type_t(), g);
			boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
			boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

			//v_op = boost::add_vertex(g);
			v_op = add_default_vertex(g, UNSIGNED_T);
			op_vertex->my_descriptor = v_op;

			func_block->op_list.insert(pair<Exp *, Un_Operation *>(exp, op_vertex));
			g_exp[v_op] = exp;
			g_vet[v_op] = OPERATION;
			g_name[v_op] = unop_label[((UnOp *) exp)->unop_type];

			if (v_target != -1) {
				add_edge_with_cap(func_block, v_target, v_op, 1, 0, g);
			}
			vtd = v_op;
		} else {
			vtd = func_block->op_list.at(exp)->my_descriptor;
		}

		break;
	}
	case CONSTANT: {
		//No Exp
		break;
	}
	case MEM: {
		vtd = ptarget_lookup(func_block, ((Mem *) exp), block, stmt);

		if (vtd == -1) {
			vtd = var_lookup(func_block, exp, block, stmt);
		}

		//If still can't find, then look for mem[] = reg and return the vtd of reg
		if (vtd == -1) {
			vtd = copy_from_reg_lookup(func_block, block, stmt, ((Mem *) exp));
		}

#ifdef DEBUG
		if(vtd != -1) {
			printf("in %s\n",exp->tostring().c_str());
		}
		printf("result: %d\n",vtd);
#endif
		break;
	}
	case TEMP: {
		if (get_reg_position(((Temp *) exp)->name) != -1) {
			/*Register*/

			/*Push register into vector & graph g, return index in vector*/
			if (push_register(func_block, (Tmp_s *) exp, g) == true) {
				vtd = func_block->reg_list.at(((Tmp_s *) exp)->index)->my_descriptor;
			}

			if (vtd != -1) {
				/*check whether it's an variable*/
				/*If so, add edge between this res and corresponding var*/
				int count;
				for (count = 0; count < func_block->variable_list.size(); count++) {
					dvariable *var = func_block->variable_list.at(count)->debug_info;
					if (var->cmp_reg(exp, func_block->stmt_block->block_list[block]->block[stmt]->asm_address) == true) {
						add_edge_with_cap(func_block, vtd, func_block->variable_list.at(count)->my_descriptor, 1, 1, g);
					}
				}

				/*check whether it contains a pointer*/
				for (count = 0; count < func_block->ptr_list.getsize(); count++) {
					if (true == func_block->ptr_list.plist.at(count)->debug_info->cmp_reg(exp, func_block->stmt_block->block_list[block]->block[stmt]->asm_address)) {
						func_block->ptr_list.plist.at(count)->copy_list.push_back((Tmp_s *) exp);
					}
				}
			}

		} else {
			/*temporary variables*/
			/*Should be translate to expressions of registers and constants, recursively*/
			/*SHOULD NOT EXIST since I have translate all temporary variables into register expression*/
		}
		break;
	}
	case PHI: {
		//No Exp
		break;
	}
	case CAST: {
		//??????
		//How to deal with cast?
		vtd = read_exp(func_block, block, stmt, ((Cast *) exp)->exp, g);
		break;
	}
	case NAME: {
		//No Exp
		break;
	}
	case UNKNOWN: {
		//No Exp
		break;
	}
	case LET: {
		//??????????
		//What's let?
		read_exp(func_block, block, stmt, ((Let *) exp)->exp, g);
		read_exp(func_block, block, stmt, ((Let *) exp)->var, g);
		read_exp(func_block, block, stmt, ((Let *) exp)->in, g);
		break;
	}
	case EXTENSION: {
		//No definition?!
		break;
	}
	default:
		break;
	}

	//if(vtd != -1){
	func_block->node_list.insert(pair<Exp *, Graph::vertex_descriptor>(exp, vtd));
	//}
	return vtd;
}

//Check whether a BinOp is correponding to an array
//op is the descriptor of the operation in BinOp
//e.g: eax99 = esp96 + 101 and esp + 101 is the location of an array -> add an edge between + and that array
bool array_loopup(fblock_ptr vine_ir_block, func_vertex_ptr func_block, int block, int stmt, Move *mov, Graph::vertex_descriptor op, Graph &g) {
	bool result;
	Exp *rexp = mov->rhs;

	switch (rexp->exp_type) {
	case BINOP: {
		BinOp *exp = (BinOp *) rexp;
		int offset = -1;
		Tmp_s * tmp;
		if (is_tmps(exp->lhs) == true && exp->rhs->exp_type == CONSTANT) {
			tmp = ((Tmp_s *) exp->lhs);
			offset = handle_constant(((Constant *) exp->rhs)->val);
		} else if (is_tmps(exp->rhs) == true && exp->lhs->exp_type == CONSTANT) {
			tmp = ((Tmp_s *) exp->rhs);
			offset = handle_constant(((Constant *) exp->lhs)->val);
		} else {
			return false;
		}

		/*Case 1: reg1 = reg2 + offset1*/
		/*1. direct access to a single-type array*/
		/*2. access of a field of a pointed struct*/
		if (exp->binop_type == PLUS && offset > 0) {
			if (offset > 0) {
				int i, j;
				for (i = 0; i < func_block->variable_list.size(); i++) {
					if (func_block->variable_list.at(i)->debug_info->original_type() == DVAR_ARRAY) {
						dbase * arr = func_block->variable_list.at(i)->debug_info;
						for (j = 0; j < arr->loclist.size(); j++) {
							if (arr->loclist.at(j)->loc_type == OFFSET_LOC) {
								offset_loc *loc = ((offset_loc *) arr->loclist.at(j));
								if (loc->offset == offset && loc->reg_name == tmp->name) {
									add_edge_with_cap(func_block, op, func_block->variable_list.at(i)->my_descriptor, 1, 1, g);
									return true;
								}
							}
						}
					}
				}

				for (i = 0; i < func_block->ptarget_list.size(); i++) {
					for (j = 0; j < func_block->ptarget_list.at(i)->debug_info_list.size(); j++) {
						address_t pc = mov->asm_address;
						if (func_block->ptarget_list.at(i)->debug_info_list.at(j)->cmp_loc(rexp, pc) == true) {
							add_edge_with_cap(func_block, op, func_block->ptarget_list.at(i)->my_descriptor, 1, 1, g);
							return true;
						}
					}
				}
				return false;
			}
		} else if (exp->binop_type == MINUS || offset < 0) {
			/*case 2: reg1 = reg2 - offset1*/
			/*indirect(?) access to a field of a struct array*/
			/*reg2 = tmp;*/

			int offset1 = offset < 0 ? (-offset) : offset;
			int current_stmt = stmt;
			int current_block = block;

			/*step1: look for reg2 = reg2' + reg3*/
			Exp *def;
			result = def_searcher(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt, tmp, def);
			if (result == false) {
				return false;
			}

			if (def->exp_type != BINOP) {
				return false;
			}

			BinOp *reg2def = (BinOp *) def;
			if (reg2def->binop_type != PLUS || is_tmps(reg2def->lhs) == false || is_tmps(reg2def->rhs) == false) {
				return false;
			}

			Tmp_s *reg2def_r = (Tmp_s *) reg2def->rhs;
			Tmp_s *reg2def_l = (Tmp_s *) reg2def->lhs;
			Tmp_s *reg3;
			if (reg2def_r->name == tmp->name) {
				reg3 = reg2def_l;
			} else if (reg2def_l->name == tmp->name) {
				reg3 = reg2def_r;
			} else {
				/*definition of reg2 is not reg2 = reg2' + reg3*/
				return false;
			}

			/*step 2: look for reg3 = esp + offset2*/
			result = def_searcher(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt, reg3, def);
			if (result == false) {
				return false;
			}

			if (def->exp_type != BINOP) {
				return false;
			}
			BinOp *reg3def = (BinOp *) def;
			if (reg3def->binop_type != PLUS) {
				return false;
			}

			Tmp_s *frame;
			int offset2;
			if (is_tmps(reg3def->lhs) == true && reg3def->rhs->exp_type == CONSTANT) {
				frame = (Tmp_s *) reg3def->lhs;
				offset2 = handle_constant(((Constant *) reg3def->rhs)->val);
			} else if (is_tmps(reg3def->rhs) == true && reg3def->lhs->exp_type == CONSTANT) {
				frame = (Tmp_s *) reg3def->rhs;
				offset2 = handle_constant(((Constant *) reg3def->lhs)->val);
			} else {
				return false;
			}
			if (frame->name != str_reg[R_ESP] && frame->name != str_reg[R_EBP]) {
				return false;
			}
			int offset_arr = offset2 - offset1;

			/*Step 3: look for an array variable whose offset is offset_loc*/
			if (offset_arr > 0) {
				int i, j;
				for (i = 0; i < func_block->variable_list.size(); i++) {
					if (func_block->variable_list.at(i)->debug_info->original_type() == DVAR_ARRAY) {
						dbase * arr = func_block->variable_list.at(i)->debug_info;

						/*Make a BinOp and check*/
						Constant *rhs = new Constant(REG_32, (unsigned) offset_arr);
						BinOp * binop = new BinOp(PLUS, frame, rhs);
						if (arr->cmp_loc(binop, vine_ir_block->block_list[current_block]->block[current_stmt]->asm_address) == true) {
							//push reg1(=tmp) into array-field variable's copy list
							Tmp_s *reg2 = ((Tmp_s *) mov->lhs);
							func_block->variable_list.at(i)->field_copy_list.push_back(reg2);
							//cout << "push " << reg2->tostring() << " to " << func_block->variable_list.at(i)->var_name << endl;
							return true; //return ture, though no edge has been added
						}
					}
				}
				return false;
			}

		}

		break;
	}
	default: {
		break;
	}
	}

}

//get the previous stmt on (SSA) stmt block
bool get_prev_stmt(fblock_ptr vine_ir_block, int block, int stmt, int *b, int *s) {
	int current_stmt;
	int current_block;
	if (stmt == 0) {
		current_block = block - 1;
		if (current_block < 0) {
			//reach the begining of function
			return false;
		}
		current_stmt = vine_ir_block->block_list[current_block]->blen - 1;

		if (current_stmt < 0) {
			return false;
		}
	} else {
		current_stmt = stmt - 1;
		current_block = block;
	}

	*b = current_block;
	*s = current_stmt;

	return true;
}

//get next stmt on (SSA) stmt block
bool get_next_stmt(fblock_ptr vine_ir_block, int block, int stmt, int *b, int *s) {
	int current_stmt;
	int current_block = block;
	if (stmt == vine_ir_block->block_list[block]->blen - 1) {
		do {
			current_block += 1;
			if (current_block > vine_ir_block->len - 1) {
				//reach the begining of function
				return false;
			}
		} while (vine_ir_block->block_list[current_block]->blen <= 0);

		current_stmt = 0;
	} else {
		current_stmt = stmt + 1;
		current_block = block;
	}

	*b = current_block;
	*s = current_stmt;

	return true;
}

//check whether offset correspond to current stmt
//Offset is the CURRENT offset before param is checked
//mem[eps + offset] = ...
bool check_param(Stmt *stmt, int offset) {
	if (stmt->stmt_type == MOVE) {
		Move *move = (Move *) stmt;
		if (move->lhs->exp_type == MEM) {
			Exp *exp = ((Mem *) move->lhs)->addr;
			if (exp->exp_type == BINOP) {
				BinOp * bop = (BinOp *) exp;
				if (bop->binop_type != PLUS) {
					return false;
				}

				Temp *temp;
				int cons;
				if (bop->lhs->exp_type == TEMP && bop->rhs->exp_type == CONSTANT) {
					temp = (Temp *) bop->lhs;
					cons = handle_constant(((Constant *) bop->rhs)->val);
				} else if (bop->rhs->exp_type == TEMP && bop->lhs->exp_type == CONSTANT) {
					temp = (Temp *) bop->rhs;
					cons = handle_constant(((Constant *) bop->lhs)->val);
				} else {
					return false;
				}

				if (offset == cons) {
					return true;
				}
			} else if (exp->exp_type == TEMP) {
				Temp *temp = (Temp *) exp;
				if (temp->name == str_reg[R_ESP] && offset == 0) {
					return true;
				} else {
					return false;
				}
			} else {
				return false;
			}
		} else {
			return false;
		}
	} else {
		return false;
	}

	return false;
}

/*map type from given DIE to variables in ptarget_list*/
bool check_call_pointer(Dwarf_Debug dbg, Dwarf_Die die, fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block, int stmt, Exp *exp, Graph &g) {
	bool result;
	int i;
	Dwarf_Die die_type;
	Dwarf_Off off_type = 0;
	result = get_die_type(dbg, die, &die_type, &off_type);
	if (result == false) {
		return false;
	}

	Dwarf_Half tag;
	result = get_die_tag(die_type, &tag);
	if (result == false) {
		return false;
	}

	/*get dvar*/
	vector<location *> null_fb;
	dvariable *source = new dvariable(dbg, die, null_fb);
	dptr * var_l = new dptr(dbg, *source, die_type, off_type, 0, (dvariable *) 0);

	switch (tag) {
	case DW_TAG_pointer_type: {
		dvariable *var_l_base;
		if (is_single_ptr(var_l, var_l_base) == true) {
			Graph::vertex_descriptor vtd = -1;
			vtd = read_exp(func_list, block, stmt, exp, g);
			if (vtd == -1) {
				/*Single in function info v.s. multiple fields in accessed variable*/
				return false;
			}

			sign_type_t sut = ((dbase *) var_l_base)->original_su;
			if (sut == SIGNED_T) {
				add_edge_with_cap(func_list, func_list->s_des, vtd, MAX_CAP, 0, g);
			} else if (sut == UNSIGNED_T) {
				add_edge_with_cap(func_list, vtd, func_list->u_des, MAX_CAP, 0, g);
			}

			return true;
		} else {
			/*struct*/
			/*set type according to name and size*/
			vector<Pointed *> ptarget_list, pstack;
			push_lib_var(var_l, ptarget_list);
			int i, j;

			//get pointer
			dptr *ptr_dbg = 0;
			Tmp_s * tmps = 0;
			Exp *def = 0;
			int current_block = block;
			int current_stmt = stmt;
			if (is_tmps(exp) == true) {
				tmps = (Tmp_s *) exp;
				result = def_searcher(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt, tmps, def);
				if (result == false) {
					//Cannot find the defination of tmps -> tmps is a new eax created after a function call
					//Therefore, return value is a pointer
					def = ((Move *) vine_ir_block->block_list[block]->block[stmt])->lhs;
					tmps = 0;
				}

				if (def->exp_type == MEM) {
					def = ((Mem *) def)->addr;
				}

			} else if (exp->exp_type == MEM) {
				def = ((Mem *) exp)->addr;
			} else {
				return false;
			}

			for (i = 0; i < func_list->ptr_list.getsize(); i++) {
				/*check ptr original location*/
				if (def != 0) {
					if (func_list->ptr_list.plist.at(i)->debug_info->cmp_loc(def, func_list->stmt_block->block_list[current_block]->block[current_stmt]->asm_address) == true) {
						/*plist.at(i) is the corresponding pointer*/
						ptr_dbg = func_list->ptr_list.plist.at(i)->debug_info;
						break;
					}
				}

				/*check copy list*/
				if (tmps != 0) {
					int j;
					for (j = 0; j < func_list->ptr_list.plist.at(i)->copy_list.size(); j++) {
						result = func_list->ptr_list.plist.at(i)->copy_list.at(j)->cmp_tmp(tmps);
						if (result == true) {
							ptr_dbg = func_list->ptr_list.plist.at(i)->debug_info;
							break;
						}
					}
				}

				/*check whether we already find the corresponding pointer in ptr_list*/
				if (ptr_dbg != 0) {
					break;
				}
			}

			if (ptr_dbg == 0) {
				return false;
			}

			/*put all children of ptr_dbg into pstack*/
			for (i = 0; i < func_list->ptarget_list.size(); i++) {
				for (j = 0; j < func_list->ptarget_list.at(i)->debug_info_list.size(); j++) {
					if (check_child(ptr_dbg, func_list->ptarget_list.at(i)->debug_info_list.at(j)) == true) {
						pstack.push_back(func_list->ptarget_list.at(i));
						break;
					}
				}
			}

			/*mapping from lib info to ptargets in pstack*/
			for (i = 0; i < ptarget_list.size(); i++) {
				for (j = 0; j < pstack.size(); j++) {
					if (pstack.at(j)->cmp_pointed(ptarget_list.at(i)) == true) {
						//Set s/u type according to ptarget_list
						sign_type_t sut = ptarget_list.at(i)->debug_info_list.at(0)->original_su;
						if (sut == SIGNED_T) {
							add_edge_with_cap(func_list, func_list->s_des, pstack.at(j)->my_descriptor, MAX_CAP, 0, g);
						} else if (sut == UNSIGNED_T) {
							add_edge_with_cap(func_list, pstack.at(j)->my_descriptor, func_list->u_des, MAX_CAP, 0, g);
						}else{
							return false;
						}
						pstack.at(j)->libdbg = true;
						//TODO: make use of this bit while printing out results
						break;
					}
				}
			}

			return true;
		}

		break;
	}
	default: {
		break;
	}
	}

	return false;
}

//whether given dptr* point to a single type (or a struct)
bool is_single_ptr(dptr *ptr, dvariable *&ret) {
	dvariable * var = ptr->var;
	while (var != 0) {
		switch (var->var_struct_type) {
		case DVAR_BASE: {
			ret = var;
			return true;
		}
		case DVAR_ARRAY: {
			var = ((darray *) var)->var;
			break;
		}
		case DVAR_STRUCT: {
			ret = var;
			return false;
		}
		case DVAR_POINTER: {
			var = ((dptr *) var)->var;
			break;
		}
		case DVAR_UN: {
			perror("DVAR_UN");
			exit(-1);
		}

		default: {
			return false;
			//break;
		}
		}
	}

	return false;
}

//Similar to push_each_pointer, but this one is for pushing ret/params of lib funcs to formal structure
void push_lib_var(dvariable *var, vector<Pointed *> &ptarget_list) {
	if (var == 0) {
		return;
	}
	switch (var->var_struct_type) {
	case DVAR_BASE: {
		dbase *base = (dbase *) var;
		//Check whether its a new pointer type
		int ptr_pos = check_ptr(var, ptarget_list);
		if (ptr_pos == -1) {
			/*Add new pointer to ptr_list*/
			string name = get_full_name(base);
			Pointed *tmp = new Pointed(base, -1, name);
			ptarget_list.push_back(tmp);
		} else {
			/*This type already exist*/
			/*Add new debug_info only*/
			ptarget_list.at(ptr_pos)->Add_into_list(base);
		}

		break;
	}
	case DVAR_STRUCT: {
		dstruct * stru = (dstruct *) var;
		int i;
		if (stru->leaf == false) {
			for (i = 0; i < stru->member_list.size(); i++) {
				if (stru->member_list.at(i) != 0) {
					push_lib_var(stru->member_list.at(i), ptarget_list);
				}
			}
		}
		break;
	}
	case DVAR_ARRAY: {
		darray * arr = (darray *) var;
		if (arr->var != 0 && arr->leaf != true) {
			push_lib_var(arr->var, ptarget_list);
		}
		break;
	}
	case DVAR_POINTER: {
		dptr * ptr = (dptr *) var;
		if (ptr->leaf == false) {
			push_lib_var(ptr->var, ptarget_list);
		}
		break;
	}
	default: {
		break;
	}
	}
}

//Following 2 functions Used by switch branches in check_call()
/*Get a parameter's descriptor in terms of a given offset value*/
bool get_xth_param(fblock_ptr vine_ir_block, int offset, int block, int stmt, int *ret_block, int *ret_stmt, Exp *&ret) {
	bool result;
	Stmt *line;
	unsigned count = 0;
	int current_block = block;
	int current_stmt = stmt;
	result = get_prev_stmt(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt);
	while (result == true) {
		line = vine_ir_block->block_list[current_block]->block[current_stmt];
		if (check_param(line, offset) == true) {
			break;
		}
		result = get_prev_stmt(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt);
	}

	if (result == false) {
		return false;
	} else {
		ret = ((Move *) line)->rhs;
		*ret_block = current_block;
		*ret_stmt = current_stmt;
		return true;
	}

}

/*get return value's node descriptor (a eax after special("call"))*/
bool get_return_value(fblock_ptr vine_ir_block, int block, int stmt, int *ret_block, int *ret_stmt, Exp *&ret) {
	bool result;
	Exp *ret_var = 0;
	int current_block = block;
	int current_stmt = stmt;
	result = get_next_stmt(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt);
	while (result != false) {
		if (vine_ir_block->block_list[current_block]->block[current_stmt]->stmt_type == MOVE) {
			Move *move = ((Move *) vine_ir_block->block_list[current_block]->block[current_stmt]);
			if (is_tmps(move->rhs) == true) {
				Tmp_s *reg = ((Tmp_s *) move->rhs);
				if (reg->name == str_reg[R_EAX] && (move->lhs->exp_type == MEM || is_tmps(move->lhs) == true)) {
					//mem[] = eax || reg = eax
					ret_var = reg;
					break;
				}
			}
		}
		result = get_next_stmt(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt);
	}

	if (result == false) {
		return false;
	} else {
		ret = ret_var;
		*ret_block = current_block;
		*ret_stmt = current_stmt;
		return true;
	}
}

//Called by switch braches in check_call()
//exp->descriptor -- s/u node
bool set_single_edge(func_vertex_ptr func_list, Exp *exp, int block, int stmt, sign_type_t signedness, Graph &g) {
	int current_block = block;
	int current_stmt = stmt;
	Graph::vertex_descriptor vtd = read_exp(func_list, current_block, current_stmt, exp, g);
	if (vtd != -1) {
		if (signedness == SIGNED_T) {
			add_edge_with_cap(func_list, func_list->s_des, vtd, MAX_CAP, 0, g);
		} else if (signedness == UNSIGNED_T) {
			add_edge_with_cap(func_list, vtd, func_list->u_des, MAX_CAP, 0, g);
		} else {
			return false;
		}
		return true;
	} else {
		return false;
	}
}
