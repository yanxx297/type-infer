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
#include "debug_info.h"
#include "vertex.h"

#include "type_dwarf_util.h"
#include "ptr_handler.h"
#include "infer.h"

using namespace std;

void dfs_min_cut(Graph::vertex_descriptor src, func_vertex_ptr func_block, Graph &g){
	//walk from src

//	taint node
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
	boost::property_map<Graph, boost::vertex_color_t>::type g_color = boost::get(boost::vertex_color, g);
	boost::property_map < Graph, boost::edge_residual_capacity_t >::type g_res = boost::get(boost::edge_residual_capacity, g);
	boost::property_map<Graph, visited_type_t>::type g_visited = boost::get(visited_type_t(), g);
	boost::property_map<Graph, signed_unsigend_type_t>::type g_sut = boost::get(signed_unsigend_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	g_color[src] = boost::red_color;
	g_visited[src] = true;

	if(g_vet[src] == VARIABLE){
		func_block->variable_list.at(g_id[src])->infered_su = SIGNED_T;
	}else if(g_vet[src] == POINTED){
		func_block->ptarget_list.at(g_id[src])->infered_su = SIGNED_T;
	}else if(g_vet[src] == OPERATION || g_vet[src] == REGISTER){
		g_sut[src] = SIGNED_T;
	}
	//printf("Set %d:%s to signed\n", src, g_name[src].c_str());
#ifdef DEBUG

	//printf("Node[%d]:%s\n",src, g_name[src].c_str());
#endif

//	walk through children, recursively
    boost::graph_traits<Graph>::edge_iterator ei, ei_end;
    for (tie(ei, ei_end) = boost::edges(g); ei != ei_end; ++ei){
    	if(source(*ei, g) == src && g_visited[target(*ei, g)]!= true){
    		if(g_res[*ei] > 0){
    			dfs_min_cut(target(*ei, g), func_block, g);
    		}
    	}
    }
}

////////////////////////////////////////////////////////////
//	Create graph
////////////////////////////////////////////////////////////

int reg_name_to_dwop(Temp * tmp){
	int result = -1;
	if(tmp->name == "R_EAX"){
		result = DW_OP_breg0;
	}else if(tmp->name == "R_ECX"){
		result = DW_OP_breg1;
	}else if(tmp->name == "R_EDX"){
		result = DW_OP_breg2;
	}else if(tmp->name == "R_EBX"){
		result = DW_OP_breg3;
	}else if(tmp->name == "R_ESP"){
		result = DW_OP_breg4;
	}else if(tmp->name == "R_EBP"){
		result = DW_OP_breg5;
	}else if(tmp->name == "R_ESI"){
		result = DW_OP_breg6;
	}else if(tmp->name == "R_EDI"){
		result = DW_OP_breg7;
	}else if(tmp->name == "R_EIP"){
		result = DW_OP_breg8;
	}else if(tmp->name == "EFLAGS"){
		result = DW_OP_breg9;
	}

	return result;
}

//Given 2 nodes of an edge, check whether this edge is already in this graph g.
bool check_duplicated_edge(int src_node, int des_node, Graph &g){
	bool result = false;

    boost::graph_traits<Graph>::edge_iterator ei, ei_end;
    for (tie(ei, ei_end) = boost::edges(g); ei != ei_end; ++ei){
    	if(source(*ei, g) == src_node &&
    			target(*ei, g) == des_node){
    		result = true;
    	}
    }
	return result;
}

void print_capacity(Graph &g){
	  boost::property_map<Graph, boost::edge_capacity_t>::type
			  capacity = boost::get(boost::edge_capacity, g);
	  boost::property_map<Graph, boost::edge_residual_capacity_t>::type
			  residual_capacity = boost::get(boost::edge_residual_capacity, g);

	  boost::graph_traits<Graph>::vertex_iterator u_iter, u_end;
	  boost::graph_traits<Graph>::out_edge_iterator ei, e_end;
	  for (tie(u_iter, u_end) = vertices(g); u_iter != u_end; ++u_iter)
		  for (tie(ei, e_end) = out_edges(*u_iter, g); ei != e_end; ++ei)
			  if (capacity[*ei] > 0)
				  std::cout << "Source: " << *u_iter << " destination: " << target(*ei, g) << " capacity: "  << capacity[*ei] << "residual cap: " << residual_capacity[*ei] << " used capacity: "
						  << (capacity[*ei] - residual_capacity[*ei]) << std::endl;
}

Traits::edge_descriptor add_edge_with_cap(Traits::vertex_descriptor &v1,
                                Traits::vertex_descriptor &v2,
                                const double capacity_fwd,
                                const double capacity_rev,
                                Graph &g){
//	Check duplicated edge
	boost::property_map < Graph, boost::edge_reverse_t >::type rev = boost::get(boost::edge_reverse, g);
	if(check_duplicated_edge(v1, v2, g) == false &&
			v1 != v2){
		  Traits::edge_descriptor e1 = add_edge(v1, v2, g).first;
		  Traits::edge_descriptor e2 = add_edge(v2, v1, g).first;
		  boost::put(boost::edge_capacity, g, e1, capacity_fwd);
		  //boost::put(boost::edge_capacity, g, e1, 0);
		  boost::put(boost::edge_capacity, g, e2, capacity_fwd);

#ifdef DEBUG
		  printf("Add edge between %d and %d\n",v1, v2);
#endif
		  rev[e1] = e2;
		  rev[e2] = e1;

		  boost::property_map < Graph, visedge_type_t >::type g_evis = boost::get(visedge_type_t(), g);
		  g_evis[e1] = true;
		  g_evis[e2] = false;
	}
}

Graph::vertex_descriptor add_default_vertex(Graph &g, sign_type_t su_type){
	Graph::vertex_descriptor vtx = boost::add_vertex(g);

//	Set default property of the vertex
	boost::property_map<Graph, signed_unsigend_type_t>::type g_su = boost::get(signed_unsigend_type_t(), g);
	boost::property_map<Graph, visible_type_t>::type g_vi = boost::get(visible_type_t(), g);

	g_su[vtx] = su_type;
	g_vi[vtx] = true;
	return vtx;
}

void print_variable_list(func_vertex_ptr *func_list, int len){
	int i ,j;
	for(i = 0; i < len; i++){
		printf("Function:%s\n",func_list[i]->func_name.c_str());
		for(j = 0 ; j < func_list[i]->variable_list.size(); j++){
			printf("\t%s\n",func_list[i]->variable_list.at(j)->debug_info->var_name.c_str());
		}
	}
}

//Chech whether the operation represented by <op> already exist in operation list (vector)
int check_duplicate_operation(func_vertex_ptr func_block, Operation *op){
	int index = -1;
	int i;

	if(op->op_type == BIN_OP){
		for(i = 0; i < func_block->op_list.size(); i++){
			if(func_block->op_list.at(i)->op_type == BIN_OP){
				if(((Bin_Operation *)func_block->op_list.at(i))->binop_type == ((Bin_Operation *)op)->binop_type
						&&((Bin_Operation *)func_block->op_list.at(i))->operand_l == ((Bin_Operation *)op)->operand_l
						&&((Bin_Operation *)func_block->op_list.at(i))->operand_r == ((Bin_Operation *)op)->operand_r){
					if(((Bin_Operation *)op)->operand_l != -1 && ((Bin_Operation *)op)->operand_r != -1){
						index = i;
						break;
					}else{
						int flag = 0;
						if(((Bin_Operation *)op)->operand_l == -1){
							if(compare_exp(((Bin_Operation *)op)->exp->lhs,((Bin_Operation *)func_block->op_list.at(i))->exp->lhs) == false){
								flag = 1;
							}
						}
						if(((Bin_Operation *)op)->operand_r == -1){
							if(compare_exp(((Bin_Operation *)op)->exp->rhs,((Bin_Operation *)func_block->op_list.at(i))->exp->rhs) == false){
								flag = 1;
							}
						}
						if(flag == 0){
							index = i;
							break;
						}
					}

				}
			}
		}
	}else if(op->op_type == UN_OP){
		for(i = 0; i < func_block->op_list.size(); i++){
			if(func_block->op_list.at(i)->op_type == UN_OP){
				if(((Un_Operation *)func_block->op_list.at(i))->unop_type == ((Un_Operation *)op)->unop_type
						&&((Un_Operation *)func_block->op_list.at(i))->operand == ((Un_Operation *)op)->operand){
					index = i;
					break;
				}
			}
		}
	}

	return index;
}

int search_by_func_name(func_vertex_ptr func_block, fblock_ptr *vine_ir_block){
	int result = -1;
	int i;
//	if(start_pos < 0 || start_pos >= cfg_funclist_length){
//		print_error("Invalid start_pos\n");
//		printf("start_pos:%d\tcfg_funclist_length:%d\n",start_pos,cfg_funclist_length);
//		exit(1);
//	}
	for(i = 0; i < cfg_funclist_length; i++ ){
		if(func_block->func_name == vine_ir_block[i]->func->name){
			result = i;
			break;
		}
	}
	return result;

}

/*Tell me whether v_des is a node of variable by traveling through variable vector*/
bool is_var(func_vertex_ptr func_block, Graph::vertex_descriptor v_des){
	bool res = false;
	int i;
	for(i = 0; i < func_block->variable_list.size(); i++){
		if(func_block->variable_list.at(i)->my_descriptor == v_des){
			res = true;
			break;
		}
	}
	return res;
}

//Find correlated variable node of a MEM exp, and return descriptor
//Return -1 if there is no such a descriptor.
int var_lookup(func_vertex_ptr func_block, Exp *exp, int block, int stmt){
	int result = -1;
	int i, j;
	exp_type_t exp_type = exp->exp_type;
	switch(exp_type){
	case MEM:{
		switch(((Mem *)exp)->addr->exp_type){
		case CONSTANT:{
			//////////////////////////////////
			//un-handle!!!!!!!!!!!!!!!!!!!!!!
			break;
		}
		//case TEMP:
		case BINOP:{
			for(i = 0; i < func_block->variable_list.size(); i++){
				dvariable *dvar = func_block->variable_list.at(i)->debug_info;
				if(dvar->cmp_loc(exp, func_block->stmt_block->block_list[block]->block[stmt]->asm_address) == true){
					result = func_block->variable_list.at(i)->my_descriptor;
					break;
				}
			}

			break;
		}
		};
		break;
	}

	default:{
		break;
	}
	}


	return result;
}

//Return whether reg_tmp is a flag register
bool is_flag(Tmp_s *reg_tmp){
	bool res = false;
	int i;
	if(reg_tmp->name == str_reg[EFLAGS]){
		res = true;
	}else{
		for(i = R_CF; i <= R_ACFLAG; i++){
			if(reg_tmp->name == str_reg[i]){
				res = true;
				break;
			}
		}
	}
	return res;
}

int push_register(func_vertex_ptr func_block, Tmp_s *reg_tmp, Graph& g){
//	Search register with certain number
//	If cannot find, push into vector, and then return index in vector
//	otherwise return vector directly

	int result = -1;
	int i;

	//Don't add flag
	if(is_flag(reg_tmp)==false){
		for(i = 0; i < func_block->reg_list.size(); i++){
			if(((Tmp_s *)func_block->reg_list.at(i)->reg_info)->index == reg_tmp->index){
				result = i;
				break;
			}
		}

		if(result == -1){
	//		register not exist
	//		push new register into vector
			boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
			boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
			boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

			//Graph::vertex_descriptor v_reg = boost::add_vertex(g);
			Graph::vertex_descriptor v_reg = add_default_vertex(g, UNSIGNED_T);
			Register *reg = new Register(reg_tmp, v_reg);
			func_block->reg_list.push_back(reg);
			result = func_block->reg_list.size() - 1;
			g_id[v_reg] = result;
			g_vet[v_reg] = REGISTER;
			g_name[v_reg] = reg_tmp->tostring();
		}
	}

	return result;
}

//Looking for a reg node that identical to target
//and return its position in reg node list (vector)
int search_reg(func_vertex_ptr func_list, Tmp_s *target){
	int result = -1;
	int i;

	for(i =0; i < func_list->reg_list.size(); i++){
		if(func_list->reg_list.at(i)->reg_info->exp_type == TEMP){
			if(get_reg_position(((Temp *)func_list->reg_list.at(i)->reg_info)->name) != -1){
				if(((Tmp_s *)(Temp *)func_list->reg_list.at(i)->reg_info)->index == target->index){
					result = i;
					break;
				}
			}
		}
	}
	return result;
}

int search_var(func_vertex_ptr func_list, int block, int stmt, Mem *target){
	int result = -1;
	int i;

	int buf = var_lookup(func_list, target, block, stmt);
	//printf("var lookup: %d\n",buf);
	if(buf != -1){
		for(i =0; i < func_list->variable_list.size(); i++){
			if(func_list->variable_list.at(i)->my_descriptor == buf ){
				result = i;
				break;
			}
		}
	}

	return result;
}

int search_op(func_vertex_ptr func_list, int block, int stmt, Exp *target){
	int result = -1;

	int i;

	switch(target->exp_type){
	case BINOP:{
		for(i= 0; i < func_list->op_list.size(); i++){
			if(func_list->op_list.at(i)->op_type == BIN_OP){
				if(((Bin_Operation *)func_list->op_list.at(i))->binop_type == ((BinOp *)target)->binop_type){

					//Check left operand
					int opr_l = -1;
					switch(((BinOp *)target)->lhs->exp_type){
					case BINOP:
					case UNOP:{
						opr_l = search_op(func_list, block, stmt, ((BinOp *)target)->lhs);
						if(opr_l != -1){
							opr_l = func_list->op_list.at(opr_l)->my_descriptor;
						}
						break;
					}
					case TEMP:{
						if(get_reg_position(((Temp *)((BinOp *)target)->lhs)->name) != -1){
							//reg
							opr_l = search_reg(func_list, ((Tmp_s *)(Temp *)((BinOp *)target)->lhs));
							if(opr_l != -1){
								opr_l = func_list->reg_list.at(opr_l)->my_descriptor;
							}
						}else{
							//var
						}
					}
					case MEM:{
						//var
						opr_l= search_var(func_list, block, stmt, (Mem *)((BinOp *)target)->lhs);
						if(opr_l != -1){
							opr_l = func_list->variable_list.at(opr_l)->my_descriptor;
						}
						break;
					}
					default:
						break;
					}

					//Check right operand
					int opr_r = -1;
					switch(((BinOp *)target)->rhs->exp_type){
					case BINOP:
					case UNOP:{
						opr_r = search_op(func_list, block, stmt, ((BinOp *)target)->rhs);
						if(opr_r != -1){
							opr_r = func_list->op_list.at(opr_r)->my_descriptor;
						}
						break;
					}
					case TEMP:{
						if(get_reg_position(((Temp *)((BinOp *)target)->rhs)->name) != -1){
							//reg
							opr_r = search_reg(func_list, ((Tmp_s *)(Temp *)((BinOp *)target)->rhs));
							if(opr_r != -1){
								opr_r = func_list->reg_list.at(opr_r)->my_descriptor;
							}
						}else{}
					}
					case MEM:{
						//var
						opr_r= search_var(func_list, block, stmt, (Mem *)((BinOp *)target)->rhs);
						if(opr_r != -1){
							opr_r = func_list->variable_list.at(opr_r)->my_descriptor;
						}
					}
					default:
						break;
					}
				}
			}
		}
		break;
	}
	case UNOP:{
		int opr = -1;
		switch(((UnOp *)target)->exp->exp_type){
		case BINOP:
		case UNOP:{
			opr = search_op(func_list, block, stmt, ((UnOp *)target)->exp);
			if(opr != -1){
				opr = func_list->op_list.at(opr)->my_descriptor;
			}
			break;
		}
		case TEMP:{
			if(get_reg_position(((Temp *)((UnOp *)target)->exp)->name) != -1){
				//reg
				opr = search_reg(func_list, ((Tmp_s *)(Temp *)((UnOp *)target)->exp));
				if(opr != -1){
					opr = func_list->reg_list.at(opr)->my_descriptor;
				}
			}else{}
		}
		case MEM:{
			//var
			opr= search_var(func_list, block, stmt, (Mem *)((UnOp *)target)->exp);
			if(opr != -1){
				opr = func_list->variable_list.at(opr)->my_descriptor;
			}
		}
		default:
			break;
		}
		break;
	}
	default:
		break;
	}

	return result;
}

//Return the descriptor of node
Graph::vertex_descriptor node_searcher(func_vertex_ptr func_list, int block, int stmt, Exp *target){
	int res = 0;
	Graph::vertex_descriptor result = -1;
	if(target->exp_type == TEMP){
		if(get_reg_position(((Temp *)target)->name) != -1){
			res = search_reg(func_list, (Tmp_s *)target);
			result = func_list->reg_list.at(res)->my_descriptor;
		}else{
		}
	}else if(target->exp_type == BINOP){
		res = search_op(func_list, block, stmt, target);
		if(res >= 0 && res < func_list->op_list.size()){
			result = func_list->op_list.at(res)->my_descriptor;
		}
		//printf("op, %d\n",result);
	}else if(target->exp_type == MEM){
		res = search_var(func_list, block, stmt, (Mem *)target);
		if(res != -1){
			result = func_list->variable_list.at(res)->my_descriptor;
		}
		//printf("var, %d\n",result);
	}

	return result;
}


//Looking for the defination of target starting from the given position
//return the Exp * of the exp equaling to target
bool def_searcher(fblock_ptr vine_ir_block, int block_no, int stmt_no, Tmp_s *target, Exp *&res){
	int i, j;
	bool result = false;
	for(i = block_no; i>0; i--){
		for(j = (i == block_no? stmt_no: (vine_ir_block->block_list[i]->blen-1)); j > 0; j--){
			if(vine_ir_block->block_list[i]->block[j]->stmt_type == MOVE){
				if(((Move *)vine_ir_block->block_list[i]->block[j])->lhs->exp_type == TEMP){
					if(get_reg_position(((Temp *)((Move *)vine_ir_block->block_list[i]->block[j])->lhs)->name) != -1){
						if(((Tmp_s *)(Temp *)((Move *)vine_ir_block->block_list[i]->block[j])->lhs)->index == target->index ||
								((Tmp_s *)(Temp *)((Move *)vine_ir_block->block_list[i]->block[j])->lhs)->name == target->name){
							res = ((Move *)vine_ir_block->block_list[i]->block[j])->rhs;
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
/*Return the corresponding nodes of var/reg/exp in the equation of SF*/
bool sf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g){
	Exp *def;
	bool result = false;
	Graph::vertex_descriptor opr_l = -1;
	Graph::vertex_descriptor opr_r = -1;
	if(get_reg_position(exp->name) == -1){
		return result;
	}else{
		if(def_searcher(vine_ir_block, block_no, stmt_no, ((Tmp_s *)exp), def) == false){
			return result;
		}else{
			//Now the defination of SF is in def
			//Get the Exp = a + b
			//printf("def: %x\n",def);
			Exp *tmp = def;
			//printf("sf_handler: %s\n",tmp->tostring().c_str());
			while(tmp->exp_type == BINOP){
				if(((BinOp *)tmp)->binop_type == MINUS){
					//tmp = a + b
					result = true;
					break;
				}else{
					if((((BinOp *)tmp)->lhs->exp_type == BINOP && ((BinOp *)tmp)->rhs->exp_type == BINOP)||
							(((BinOp *)tmp)->lhs->exp_type != BINOP && ((BinOp *)tmp)->rhs->exp_type != BINOP)){
						result = false;
						return result;
					}else if(((BinOp *)tmp)->lhs->exp_type == BINOP && ((BinOp *)tmp)->rhs->exp_type != BINOP){
						tmp = ((BinOp *)tmp)->lhs;
						//break;
					}else if(((BinOp *)tmp)->rhs->exp_type == BINOP && ((BinOp *)tmp)->lhs->exp_type != BINOP){
						tmp = ((BinOp *)tmp)->rhs;
						//break;
					}
				}
			}

			//Now tmp = a + b
			//Lookup a and b in graph, and connect them to signed node
			//printf("tmp: %s\n",tmp->tostring().c_str());
			if(((BinOp *)tmp)->lhs != 0){
				opr_l = node_searcher(func_list, block_no, stmt_no, ((BinOp *)tmp)->lhs);
				if(opr_l != -1){
					add_edge_with_cap(func_list->s_des, opr_l, MAX_CAP, 0, g);
				}
			}
			if(((BinOp *)tmp)->rhs != 0){
				opr_r = node_searcher(func_list, block_no, stmt_no, ((BinOp *)tmp)->rhs);
				if(opr_r != -1){
					add_edge_with_cap(func_list->s_des, opr_r, MAX_CAP, 0, g);
				}
			}

			//connect a and b to signed node
//			if(opr_l != -1 && opr_r != -1){
//				add_edge_with_cap(func_list->s_des, opr_l, MAX_CAP, 0, g);
//				add_edge_with_cap(func_list->s_des, opr_r, MAX_CAP, 0, g);
//			}

		}
	}

	return result;
}

//Similar to sf_handler except:
//1. CF = a<b
//2. unsigned
bool cf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g){
	Exp *def;
	bool result = false;
	Graph::vertex_descriptor opr_l = -1;
	Graph::vertex_descriptor opr_r = -1;
	if(get_reg_position(exp->name) == -1){
		return result;
	}else{
		if(def_searcher(vine_ir_block, block_no, stmt_no, ((Tmp_s *)exp), def) == false){
			return result;
		}else{
			//Now the defination of CF is in def
			//Get the Exp = a < b
			Exp *tmp = def;
			printf("cf_handler: %s\n",tmp->tostring().c_str());
			while(tmp->exp_type == BINOP){
				if(((BinOp *)tmp)->binop_type == LT){
					//tmp = a < b
					result = true;
					break;
				}else{
					if((((BinOp *)tmp)->lhs->exp_type == BINOP && ((BinOp *)tmp)->rhs->exp_type == BINOP)||
							(((BinOp *)tmp)->lhs->exp_type != BINOP && ((BinOp *)tmp)->rhs->exp_type != BINOP)){
						result = false;
						return result;
					}else if(((BinOp *)tmp)->lhs->exp_type == BINOP && ((BinOp *)tmp)->rhs->exp_type != BINOP){
						tmp = ((BinOp *)tmp)->lhs;
						//break;
					}else if(((BinOp *)tmp)->rhs->exp_type == BINOP && ((BinOp *)tmp)->lhs->exp_type != BINOP){
						tmp = ((BinOp *)tmp)->rhs;
						//break;
					}
				}
			}

			//Now tmp = a + b
			//Lookup a and b in graph, and connect them to unsigned node
			if(((BinOp *)tmp)->lhs != 0){
				opr_l = node_searcher(func_list, block_no, stmt_no, ((BinOp *)tmp)->lhs);
				if(opr_l != -1){
					add_edge_with_cap(opr_l, func_list->u_des, MAX_CAP, 0, g);
				}
			}
			if(((BinOp *)tmp)->rhs != 0){
				opr_r = node_searcher(func_list, block_no, stmt_no, ((BinOp *)tmp)->rhs);
				if(opr_r != -1){
					add_edge_with_cap(opr_r, func_list->u_des, MAX_CAP, 0, g);
				}
			}

			//connect a and b to unsigned node
//			if(opr_l != -1 && opr_r != -1){
//				add_edge_with_cap(opr_l, func_list->u_des, MAX_CAP, 0, g);
//				add_edge_with_cap(opr_r, func_list->u_des, MAX_CAP, 0, g);
//			}

		}
	}

	return result;
}


//Handle the 2 operands of smod.
//var/register connect to signed node
//operand_binop and operand_var are descriptors
void smod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var,  Graph& g){
	//Handle bin_op
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	if(func_block->op_list.at(g_id[operand_binop])->op_type == BIN_OP){
		if(((Bin_Operation *)func_block->op_list.at(g_id[operand_binop]))->binop_type == BITOR){
			Graph::vertex_descriptor opr_l = ((Bin_Operation *)func_block->op_list.at(g_id[operand_binop]))->operand_l;
			Graph::vertex_descriptor opr_r = ((Bin_Operation *)func_block->op_list.at(g_id[operand_binop]))->operand_r;
			if(g_vet[opr_l] == OPERATION && (g_vet[opr_r] == REGISTER || g_vet[opr_r] == VARIABLE)){
				cout<<"set "<<g_name[opr_l]<<" to sigend (%$)"<<endl;
				add_edge_with_cap(func_block->s_des , opr_r, MAX_CAP, 0, g);
			}else if(g_vet[opr_r] == OPERATION && (g_vet[opr_l] == REGISTER || g_vet[opr_l] == VARIABLE)){
				cout<<"set "<<g_name[opr_r]<<" to sigend (%$)"<<endl;
				add_edge_with_cap(func_block->s_des ,opr_l, MAX_CAP, 0, g);
			}

		}
	}

	//Handle var/register
	add_edge_with_cap(func_block->s_des, operand_var, MAX_CAP, 0, g);
}

void handle_smod(func_vertex_ptr func_block, int descriptor, Graph& g){
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	if(func_block->op_list.at(g_id[descriptor])->op_type == BIN_OP){
		if(((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->binop_type == SMOD){
			int op_l = ((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->operand_l;
			int op_r = ((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->operand_r;
			if(op_l != -1 && op_r != -1){
				if(g_vet[op_l] == OPERATION && (g_vet[op_r] == VARIABLE || g_vet[op_r] == REGISTER)){
					if(func_block->op_list.at(g_id[op_l])->op_type == BIN_OP){
						smod_operand_handler(func_block, op_l, op_r, g);
					}
				}else if(g_vet[op_r] == OPERATION && (g_vet[op_l] == VARIABLE || g_vet[op_l] == REGISTER)){
					if(func_block->op_list.at(g_id[op_r])->op_type == BIN_OP){
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
void mod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var,  Graph& g){
	//Handle bin_op
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	if(func_block->op_list.at(g_id[operand_binop])->op_type == BIN_OP){
		if(((Bin_Operation *)func_block->op_list.at(g_id[operand_binop]))->binop_type == BITOR){
			Graph::vertex_descriptor opr_l = ((Bin_Operation *)func_block->op_list.at(g_id[operand_binop]))->operand_l;
			Graph::vertex_descriptor opr_r = ((Bin_Operation *)func_block->op_list.at(g_id[operand_binop]))->operand_r;
			//printf("left:%s\tright:%s\n",g_name[opr_l].c_str(),g_name[opr_r].c_str());
			if(g_vet[opr_l] == OPERATION && (g_vet[opr_r] == REGISTER || g_vet[opr_r] == VARIABLE)){
				add_edge_with_cap(opr_r, func_block->u_des , MAX_CAP, 0, g);
				cout<<"set "<<g_name[opr_r]<<" to unsigend (%)"<<endl;
				//printf("Add edge\n");
			}else if(g_vet[opr_r] == OPERATION && (g_vet[opr_l] == REGISTER || g_vet[opr_l] == VARIABLE)){
				add_edge_with_cap(opr_l, func_block->u_des , MAX_CAP, 0, g);
				cout<<"set "<<g_name[opr_l]<<" to unsigend (%)"<<endl;
				//printf("Add edge\n");
			}else{
				//printf("Not a valid %\n");
			}

		}
	}

	//Handle var/register
	add_edge_with_cap(operand_var, func_block->u_des ,MAX_CAP, 0, g);
}

//descriptor is the descriptor of % operation
void handle_mod(func_vertex_ptr func_block, int descriptor, Graph& g){
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	if(func_block->op_list.at(g_id[descriptor])->op_type == BIN_OP){
		if(((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->binop_type == MOD){
			int op_l = ((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->operand_l;
			int op_r = ((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->operand_r;
			if(op_l != -1 && op_r != -1){
				if(g_vet[op_l] == OPERATION && (g_vet[op_r] == VARIABLE || g_vet[op_r] == REGISTER)){
					if(func_block->op_list.at(g_id[op_l])->op_type == BIN_OP){
						mod_operand_handler(func_block, op_l, op_r, g);
					}
				}else if(g_vet[op_r] == OPERATION && (g_vet[op_l] == VARIABLE || g_vet[op_l] == REGISTER)){
					if(func_block->op_list.at(g_id[op_r])->op_type == BIN_OP){
						mod_operand_handler(func_block, op_r, op_l, g);
					}
				}
			}
		}
	}
}

void handle_sar(func_vertex_ptr func_block, int descriptor, Graph& g){
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	if(func_block->op_list.at(g_id[descriptor])->op_type == BIN_OP){
		if(((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->binop_type == ARSHIFT){
			Graph::vertex_descriptor op_l = ((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->operand_l;
			if(op_l != -1){
				if(g_vet[op_l] == VARIABLE){
					if(func_block->variable_list.at(g_id[op_l])->debug_info->var_length == 4){
						add_edge_with_cap(func_block->s_des, op_l, MAX_CAP, 0, g);
						cout<<"set "<<g_name[op_l]<<" to sigend ($>>)"<<endl;
					}
				}else if(g_vet[op_l] == REGISTER){
					if(func_block->reg_list.at(g_id[op_l])->reg_info->exp_type == TEMP){
						if(((Temp *)func_block->reg_list.at(g_id[op_l])->reg_info)->typ == REG_32){
							add_edge_with_cap(func_block->s_des, op_l, MAX_CAP, 0, g);
							cout<<"set "<<g_name[op_l]<<" to sigend ($>>)"<<endl;
						}
					}
				}else if(g_vet[op_l] == OPERATION){
					//!!!!!!!
					//How to handle Exp?
					//add_edge_with_cap(func_block->s_des, op_l, rev, MAX_CAP, 0, g);
				}
			}
		}
	}
}

void handle_shr(func_vertex_ptr func_block, int descriptor, Graph& g){
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);

	/*Test whether its a shr in flag computing*/
	/*If so, don't handle it.*/
	int stmt, block;
	stmt = func_block->op_list.at(g_id[descriptor])->stmt_number;
	block = func_block->op_list.at(g_id[descriptor])->block_number;
	Stmt *tmp = func_block->stmt_block->block_list[block]->block[stmt];
	if(tmp->stmt_type == MOVE){
		Move *tmp_mv = (Move *)tmp;
		if(is_tmps(tmp_mv->lhs) == true){
			Tmp_s * tmps = (Tmp_s *)tmp_mv->lhs;
			if(is_flag(tmps)){
				return;
			}
		}
	}

	if(func_block->op_list.at(g_id[descriptor])->op_type == BIN_OP){
		if(((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->binop_type == RSHIFT){
			Graph::vertex_descriptor op_l = ((Bin_Operation *)func_block->op_list.at(g_id[descriptor]))->operand_l;
			if(op_l != -1){
				if(g_vet[op_l] == VARIABLE){
					if(func_block->variable_list.at(g_id[op_l])->debug_info->var_length == 4){
						add_edge_with_cap(op_l, func_block->u_des, MAX_CAP, 0, g);
						cout<<"set "<<g_name[op_l]<<"to unsigend (>>)"<<endl;
					}
				}else if(g_vet[op_l] == REGISTER){
					if(func_block->reg_list.at(g_id[op_l])->reg_info->exp_type == TEMP){
						if(((Temp *)func_block->reg_list.at(g_id[op_l])->reg_info)->typ == REG_32){
							add_edge_with_cap(op_l, func_block->u_des, MAX_CAP, 0, g);
							cout<<"set "<<g_name[op_l]<<"to unsigend (>>)"<<endl;
						}
					}
				}else if(g_vet[op_l] == OPERATION){
					//!!!!!!!
					//How to handle Exp?
					//add_edge_with_cap(op_l, func_block->u_des, rev, MAX_CAP, 0, g);
				}
			}
		}
	}
}

void handle_operation(func_vertex_ptr func_block, Graph& g){
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

	pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	if(g_vet[*vp.first] == OPERATION){
    		int node_id = g_id[*vp.first];
    		if(func_block->op_list.at(node_id)->op_type == BIN_OP){
    			switch(((Bin_Operation *)func_block->op_list.at(node_id))->binop_type){
    			case SMOD:{
    				//printf("handle smod\n");
    				handle_smod(func_block, *vp.first, g);
    				break;
    			}
    			case MOD:{
    				//printf("handle mod\n");
    				handle_mod(func_block, *vp.first, g);
    				break;
    			}
    			case ARSHIFT:{
    				//printf("handle arshift\n");
    				handle_sar(func_block, *vp.first, g);
    				break;
    			}
    			case RSHIFT:{
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

void check_cjmp(fblock_ptr vine_ir_block, func_vertex_ptr func_list, Exp *cond, int block_no, int stmt_no, Graph& g){
//	Look for <, <=, >, >= and add edges to signed/unsigend node
//	cond is the condition of the cjmp
	Exp *tmp = cond;
	while(tmp->exp_type == CAST){
		tmp = ((Cast *)tmp)->exp;
	}

//	Now tmp is a binOp or unOp
	switch(tmp->exp_type){
	case BINOP:{
		switch(((BinOp *)tmp)->binop_type){
		case BITOR:{
			if(((BinOp *)tmp)->rhs->exp_type == TEMP){
				if(((Temp *)((BinOp *)tmp)->rhs)->name == str_reg[R_ZF]){
					if(((BinOp *)tmp)->lhs->exp_type == BINOP){
						if(((BinOp *)((BinOp *)tmp)->lhs)->binop_type == XOR){
							if(((BinOp *)((BinOp *)tmp)->lhs)->lhs->exp_type == TEMP ||
									((BinOp *)((BinOp *)tmp)->lhs)->rhs->exp_type == TEMP){
								if(((Temp *)((BinOp *)((BinOp *)tmp)->lhs)->lhs)->name == str_reg[R_SF] ||
										((Temp *)((BinOp *)((BinOp *)tmp)->lhs)->rhs)->name == str_reg[R_OF]){
									//SF^OF | ZF
									//jle or jg
									sf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *)((BinOp *)((BinOp *)tmp)->lhs)->lhs, g);
								}
							}
						}
					}else if(((BinOp *)tmp)->lhs->exp_type == TEMP){
						if(((Temp *)((BinOp *)tmp)->lhs)->name == str_reg[R_CF]){
							//CF | ZF
							//jbe or ja
							cf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *)((BinOp *)tmp)->lhs, g);
						}
					}
				}
			}
			break;
		}
		case XOR:{
			if(((BinOp *)tmp)->lhs->exp_type == TEMP ||
					((BinOp *)tmp)->rhs->exp_type == TEMP){
				if(((Temp *)((BinOp *)tmp)->lhs)->name == str_reg[R_SF] ||
						((Temp *)((BinOp *)tmp)->rhs)->name == str_reg[R_OF]){
					//SF^OF
					//jl or jge
					sf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *)((BinOp *)tmp)->lhs, g);
				}
			}
			break;
		}
		default:
			break;
		}
		break;
	}
	case TEMP:{
		//CF
		if(((Temp *)tmp)->name == str_reg[R_CF]){
			//jae or jb
			cf_handler(vine_ir_block, func_list, block_no, stmt_no, (Temp *)tmp, g);
		}
		break;
	}
	default:
		break;
	}
}

bool compare_mem(Mem *former, Mem *latter){
	//Check whether the 2 Mem* represent the same location
	bool result = false;
	if(former->addr->exp_type != latter->addr->exp_type){
		result = false;
	}else{
		if(former->addr->exp_type == BINOP){
			if(((BinOp *)former->addr)->lhs->exp_type == TEMP &&
					((BinOp *)former->addr)->rhs->exp_type == CONSTANT &&
					((BinOp *)latter->addr)->lhs->exp_type == TEMP &&
					((BinOp *)latter->addr)->rhs->exp_type == CONSTANT){
				if(((Tmp_s *)((BinOp *)former->addr)->lhs)->index == ((Tmp_s *)((BinOp *)latter->addr)->lhs)->index &&
						((Constant *)((BinOp *)former->addr)->rhs)->val == ((Constant *)((BinOp *)latter->addr)->rhs)->val){
					result = true;
				}
			}
		}else if(former->addr->exp_type == TEMP){
			if(get_reg_position(((Temp *)former->addr)->name) != -1 &&
					get_reg_position(((Temp *)latter->addr)->name) != -1 ){
				if(((Tmp_s *)former->addr)->index == ((Tmp_s *)latter->addr)->index){
					result = true;
				}
			}
		}
	}
	return result;
}

//Compare 2 Exp* that return -1 as descriptor, include:
//1-mem[] whose corresponding variable node
//2-constant, which is not included in graoh by default
//3-?????
bool compare_exp(Exp *former, Exp *latter){
	bool result = false;
	if(former->exp_type != latter->exp_type){
		return result;
	}else{
		exp_type_t type = former->exp_type;
		switch(type){
		case MEM:{
			result = compare_mem((Mem *)former, (Mem *)latter);
			break;
		}
		case CONSTANT:{
			if(((Constant *)former)->val == ((Constant *)latter)->val){
				result = true;
			}
			break;
		}
		default:{
			break;
		}
		}
	}
	return result;
}

//Return s/u type by reading a Dwarf_Unsigned
sign_type_t get_su_type(Dwarf_Unsigned su_type){
	sign_type_t result = UNKNOW_T;
	if(su_type == DW_ATE_unsigned || su_type == DW_ATE_unsigned_char){
		result = UNSIGNED_T;
	}else if(su_type == DW_ATE_signed || su_type == DW_ATE_signed_char){
		result = SIGNED_T;
	}

	return result;
}

//function: get the full name of a base variable recursively
string get_full_name(dbase *var){
	dvariable *tmp = var;
	string result = var->var_name;
	tmp = tmp->parent;
	while(tmp != 0){
		switch(tmp->var_struct_type){
		case DVAR_POINTER:{
			if(tmp->parent == 0){
				result = "*" + result;
			}else{
				result = "->" + result;
			}
			break;
		}
		case DVAR_STRUCT:{
			if(tmp->parent != 0){
				if(tmp->parent->var_struct_type == DVAR_ARRAY){
					break;
				}else{
					result = tmp->var_name + "." + result;
				}
			}else{
				result = tmp->var_name + "." + result;
			}
			break;
		}
		case DVAR_BASE:{
			break;
		}
		default:{
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
void check_movzsbl(func_vertex_ptr func_list, Cast *src, Temp *dst, Graph::vertex_descriptor v_src, Graph &g){
	if(src->exp->exp_type == MEM){
		Mem *m_src = (Mem *)src->exp;
		if(m_src->typ < dst->typ){
			if(src->cast_type == CAST_SIGNED){
				//movsbl -> signed
				add_edge_with_cap(func_list->s_des,v_src, MAX_CAP, 0, g);
			}else if(src->cast_type == CAST_UNSIGNED){
				//movzbl -> unsigned
				add_edge_with_cap(v_src, func_list->u_des, MAX_CAP, 0, g);
			}else{
				//neither
				//do nothing
			}
		}
	}
}

//Set signed/unsigned of function params and return value according to function name
//Use dbg info or harded coded assignment based on existed knowledge
void check_call(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block, int stmt, string func_name, Graph &g){
	int i;
	int res = -1;
	for(i = IFUNC_STRCAT; i <= IFUNC_WMEMCMP; i++){
		if(func_name == indirect[i]){
			res = i;
			break;
		}
	}

	if(res == -1){
		//No need to hardcode types
		//read dbg info and map types
		int res = -1;
		Dwarf_Die subprog;
		Dwarf_Debug dbg = 0;
	    Dwarf_Error error;
	    Dwarf_Handler errhand = 0;
	    Dwarf_Ptr errarg = 0;
	    bool result = false;
	    int fd = open(DBGLIB,O_RDONLY);
	    if(fd < 0) {
	        printf("Failure attempting to open \"%s\"\n",DBGLIB);
	    }
	    res = dwarf_init(fd,DW_DLC_READ,errhand,errarg, &dbg,&error);
	    if(res != DW_DLV_OK) {
	        printf("Giving up, cannot do DWARF processing\n");
	        exit(1);
	    }
	    result = libcdbg_read_cu(dbg, func_name, &subprog);
	    if(result == true){
	    	//DIE Getchu!
    		int current_stmt;
    		int current_block;

	    	//1 Check type of return value
	    	//get result exp

    		Mem *ret_var = 0;
	    	result = get_next_stmt(vine_ir_block, block, stmt, &current_block, &current_stmt);
	    	while(result != false){
	    		//mem[] = eax, get mem[]
	    		if(vine_ir_block->block_list[current_block]->block[current_stmt]->stmt_type == MOVE){
	    			Move *move = ((Move *)vine_ir_block->block_list[current_block]->block[current_stmt]);
	    			if(is_tmps(move->rhs) == true){
	    				Tmp_s *reg = ((Tmp_s *)move->rhs);
	    				if(reg->name == str_reg[R_EAX] && move->lhs->exp_type == MEM){
	    					ret_var = ((Mem *)move->lhs);
	    					break;
	    				}
	    			}
	    		}
	    		result = get_next_stmt(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt);
	    	}

	    	if(result == false){
	    		/*It may happen that the ret value is not used in this program*/
	    		/*e.g. fclose(fp)*/
//	    		perror("cannot find return value");
//	    		exit(-1);
	    	}else{
		    	/*set edge of ret value*/
		    	set_edge(func_list, dbg, subprog, current_block, current_stmt, NULL, ret_var, g);
	    	}

    		//-------------------------------------------------------------------------------------------X
    		//2 check type of each param
    		Dwarf_Die param;
    		int offset = 0;
    		sign_type_t su_param;
    		result = get_prev_stmt(vine_ir_block, block, stmt, &current_block, &current_stmt);

    		res = dwarf_child(subprog, &param, &error);
    		while(res == DW_DLV_OK){
    			//check tag = DW_TAG_formal_parameter
    			Dwarf_Half child_tag;
    			if(get_die_tag(param, &child_tag) != true){
    				//next child
    			}else{
    				if(child_tag != DW_TAG_formal_parameter){
    					//next child
    				}else{
    					while(result == true){
    						//get_prev_stmt() return false if reach the beginning of func
    	    				//check whether param correspond to current stmt
    	    				if(check_param(vine_ir_block->block_list[current_block]->block[current_stmt], offset) == true){
    	    					Exp *current_exp = ((Move *)vine_ir_block->block_list[current_block]->block[current_stmt])->rhs;
    	    					set_edge(func_list, dbg, param, current_block, current_stmt, &offset, current_exp, g);
    	    					break;
    	    				}else{
    	    					//go next
    	    				}

    	    				result = get_prev_stmt(vine_ir_block, current_block, current_stmt, &current_block, &current_stmt);
    	    			}
    				}
    			}
    			res = dwarf_siblingof(dbg, param, &param, &error);
    		}
	    }
	}else{
		//indirect function
		//hardcode types of params and return value
		switch(res){
		case IFUNC_STRCAT:{
			break;
		}
		case IFUNC_INDEX:{
			break;
		}
		case IFUNC_STRCMP:{
			break;
		}
		case IFUNC_STRCPY:{
			break;
		}
		case IFUNC_STRCSPN:{
			break;
		}
		case IFUNC_STRLEN:{
			break;
		}
		case IFUNC_STRNLEN:{
			break;
		}
		case IFUNC_STRNCAT:{
			break;
		}
		case IFUNC_STRNCMP:{
			break;
		}
		case IFUNC_STRNCPY:{
			break;
		}
		case IFUNC_RINDEX:{
			break;
		}
		case IFUNC_STRPBRK:{
			break;
		}
		case IFUNC_STRSPN:{
			break;
		}
		case IFUNC_MEMCHR:{
			break;
		}
		case IFUNC_BCMP:{
			break;
		}
		case IFUNC_MEMMOVE:{
			break;
		}
		case IFUNC_MEMSET:{
			break;
		}
		case IFUNC_MEMPCPY:{
			break;
		}
		case IFUNC_BCOPY:{
			break;
		}
		case IFUNC_BZERO:{
			break;
		}
		case IFUNC_STPCPY:{
			break;
		}
		case IFUNC_STPNCPY:{
			break;
		}
		case IFUNC_STRCASECMP:{
			break;
		}
		case IFUNC_STRNCASECMP:{
			break;
		}
		case IFUNC_MEMCPY:{
			break;
		}
		case IFUNC_RAWMEMCHR:{
			break;
		}
		case IFUNC_MEMRCHR:{
			break;
		}
		case IFUNC_STRSTR:{
			break;
		}
		case IFUNC_STRCASESTR:{
			break;
		}
		case IFUNC_WCSCHR:{
			break;
		}
		case IFUNC_WCSCMP:{
			break;
		}
		case IFUNC_WCSCPY:{
			break;
		}
		case IFUNC_WCSLEN:{
			break;
		}
		case IFUNC_WCSRCHR:{
			break;
		}
		case IFUNC_WMEMCMP:{
			break;
		}
		default:{
			break;
		}
		}
	}
}

//Set edges of a param/ret according to Die
bool set_edge(func_vertex_ptr func_list,Dwarf_Debug dbg, Dwarf_Die param, int block, int stmt, int *new_offset, Exp *current_exp, Graph &g){
	bool result;
	sign_type_t su_param;
	int length;
	//set s/u
	result = get_su(dbg, param, &su_param);
	if(result == false){
		check_call_pointer(dbg, param, func_list, block, stmt, current_exp, g);
	}else{
		Graph::vertex_descriptor vtd = -1;
		vtd = read_exp(func_list, block, stmt, current_exp, g);
		if(vtd != -1){
			if(su_param == SIGNED_T){
				cout<<current_exp->tostring()<<"is signed because of libc info"<<endl;
				add_edge_with_cap(func_list->s_des, vtd, MAX_CAP, 0, g);
			}else if(su_param == UNSIGNED_T){
				cout<<current_exp->tostring()<<"is unsigned because of libc info"<<endl;
				add_edge_with_cap(vtd, func_list->u_des, MAX_CAP, 0, g);
			}else{
				perror("UNKNOWN type parameter\n");
			}
		}else{
			perror("NO corresponding vertice for this exp\n");
			//FIXME: no corresponding vertice for this exp
			//Left not handled
		}
	}

	// update offset
	result = get_length(dbg, param, &length);
	if(result == false){
		if(new_offset != 0){
			char offstr[128];
			sprintf(offstr, "%d", *new_offset);
			string errmsg = "cannot get length of param at eps+"+std::string(offstr);
			perror(errmsg.c_str());
		}else{
			perror("cannot get length of ret value");
		}

		return false;
	}

	//new_offset is NULL if the caller send a ret value
	if(new_offset != 0){
		*new_offset += length;
	}

	return true;
}

Graph::vertex_descriptor read_exp(func_vertex_ptr func_block, int block, int stmt, Exp *exp, Graph& g){
	int op_id;
	Graph::vertex_descriptor vtd = -1;
	switch(exp->exp_type){
	case BINOP:{
		//Don't add this operation to graph if both operands are constant
		if(((BinOp *)exp)->lhs->exp_type == CONSTANT && ((BinOp *)exp)->rhs->exp_type == CONSTANT ){
			break;
		}

		Graph::vertex_descriptor v_l;
		//= boost::add_vertex(g);
		Graph::vertex_descriptor v_r;
		Graph::vertex_descriptor v_op = -1;
		//= boost::add_vertex(g);
		v_l = read_exp(func_block, block, stmt, ((BinOp *) exp)->lhs, g);
		v_r = read_exp(func_block, block, stmt, ((BinOp *) exp)->rhs, g);

		Bin_Operation *op_vertex = new Bin_Operation(((BinOp *)exp)->binop_type, v_l, v_r, v_op, (BinOp *)exp, block, stmt);



		/*Check duplicate operation*/
		op_id = check_duplicate_operation(func_block, op_vertex);
		if(op_id == -1){
			//No duplicate
			boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
			boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
			boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

			//v_op= boost::add_vertex(g);
			v_op= add_default_vertex(g, UNSIGNED_T);
			op_vertex->my_descriptor = v_op;

			func_block->op_list.push_back(op_vertex);
			g_id[v_op] = func_block->op_list.size() - 1;
			g_vet[v_op] = OPERATION;

			char number[256];
			sprintf(number, "%d", v_op);
			string number_str = std::string(number);
			g_name[v_op] = number_str + ":" +binop_label[((BinOp *)exp)->binop_type];

			//printf("\t%d -> %d\n",v_l, v_op);
			//printf("\t%d -> %d\n",v_r, v_op);
			if(v_l != -1){
				add_edge_with_cap(v_l, v_op, 1, 0, g);
			}
			if(v_r != -1){
				add_edge_with_cap(v_r, v_op, 1, 0, g);
			}


			vtd = v_op;
		}else{
			//Duplicate.
			vtd = func_block->op_list.at(op_id)->my_descriptor;
		}

		//Handle smod there (% and /)


		break;
	}
	case UNOP:{
		//Don't add this operation to graph if the operand is an constant
		if(((UnOp *)exp)->exp->exp_type == CONSTANT){
			break;
		}

		Graph::vertex_descriptor v_target;
		Graph::vertex_descriptor v_op = -1;
		v_target = read_exp(func_block, block, stmt, ((UnOp *) exp)->exp, g);

		Un_Operation *op_vertex = new Un_Operation(((UnOp *) exp)->unop_type, v_target, v_op, block, stmt);

		op_id = check_duplicate_operation(func_block, op_vertex);
		if(op_id == -1){
			boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
			boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
			boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

			//v_op = boost::add_vertex(g);
			v_op = add_default_vertex(g, UNSIGNED_T);
			op_vertex->my_descriptor = v_op;

			func_block->op_list.push_back(op_vertex);
			g_id[v_op] = func_block->op_list.size() - 1;
			g_vet[v_op] = OPERATION;
			g_name[v_op] = unop_label[((UnOp *)exp)->unop_type];

			if(v_target != -1){
				add_edge_with_cap(v_target, v_op, 1, 0, g);
			}
			vtd = v_op;
		}else{
			vtd = func_block->op_list.at(op_id)->my_descriptor;
		}

		break;
	}
	case CONSTANT:{
		//No Exp
		break;
	}
	case MEM:{
		vtd = ptarget_lookup(func_block, ((Mem *)exp), block, stmt);

		if(vtd == -1){
			vtd = var_lookup(func_block, exp, block, stmt);
		}

		//If still can't find, then look for mem[] = reg and return the vtd of reg
		if(vtd == -1){
			vtd = copy_from_reg_lookup(func_block, block, stmt, ((Mem *)exp));
		}

#ifdef DEBUG
		if(vtd != -1){
			printf("in %s\n",exp->tostring().c_str());
		}
		printf("result: %d\n",vtd);
#endif
		break;
	}
	case TEMP:{
		if(get_reg_position(((Temp *)exp)->name) != -1){
			/*Register*/

			/*Push register into vector & graph g, return index in vector*/
			int index = push_register(func_block, (Tmp_s *)exp, g);
			if(index != -1){
				vtd = func_block->reg_list.at(index)->my_descriptor;
			}

			/*check whether it's an variable*/
			/*If so, add edge between this res and corresponding var*/
			if(vtd != -1){
				int count;
				for(count = 0; count < func_block->variable_list.size(); count ++){
					dvariable *var = func_block->variable_list.at(count)->debug_info;
					if(var->cmp_reg(exp, func_block->stmt_block->block_list[block]->block[stmt]->asm_address) == true){
						//cout<<func_block->stmt_block->block_list[block]->block[stmt]->tostring()<<endl;
						add_edge_with_cap(vtd, func_block->variable_list.at(count)->my_descriptor, 1, 1, g);
					}
				}
			}

		}else{
			/*temporary variables*/
			/*Should be translate to expressions of registers and constants, recursively*/
			/*SHOULD NOT EXIST since I have translate all temporary variables into register expression*/
		}
		break;
	}
	case PHI:{
		//No Exp
		break;
	}
	case CAST:{
		//??????
		//How to deal with cast?
		vtd = read_exp(func_block, block, stmt, ((Cast *) exp)->exp, g);
		break;
	}
	case NAME:{
		//No Exp
		break;
	}
	case UNKNOWN:{
		//No Exp
		break;
	}
	case LET:{
		//??????????
		//What's let?
		read_exp(func_block, block, stmt, ((Let *) exp)->exp, g);
		read_exp(func_block, block, stmt, ((Let *) exp)->var, g);
		read_exp(func_block, block, stmt, ((Let *) exp)->in, g);
		break;
	}
	case EXTENSION:{
		//No definition?!
		break;
	}
	default:
		break;
	}
	return vtd;
}

//get the previous stmt on (SSA) stmt block
bool get_prev_stmt(fblock_ptr vine_ir_block, int block, int stmt, int *b, int *s){
	int current_stmt;
	int current_block;
	if(stmt == 0){
		current_block = block - 1;
		if(current_block < 0){
			//reach the begining of function
			return false;
		}
		current_stmt = vine_ir_block->block_list[current_block]->blen-1;

		if(current_stmt < 0){
			return false;
		}
	}else{
		current_stmt = stmt -1;
		current_block = block;
	}

	*b = current_block;
	*s = current_stmt;

	return true;
}

//get next stmt on (SSA) stmt block
bool get_next_stmt(fblock_ptr vine_ir_block, int block, int stmt, int *b, int *s){
	int current_stmt;
	int current_block = block;
	if(stmt == vine_ir_block->block_list[block]->blen-1){
		do{
			current_block += 1;
			if(current_block > vine_ir_block->len - 1){
				//reach the begining of function
				return false;
			}
		}while(vine_ir_block->block_list[current_block]->blen <= 0);

		current_stmt = 0;
	}else{
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
bool check_param(Stmt *stmt, int offset){
	if(stmt->stmt_type == MOVE){
		Move *move = (Move *)stmt;
		if(move->lhs->exp_type == MEM){
			Exp *exp = ((Mem *)move->lhs)->addr;
			if(exp->exp_type == BINOP){
				BinOp * bop = (BinOp *)exp;
				if(bop->binop_type != PLUS){
					return false;
				}

				Temp *temp;
				int cons;
				if(bop->lhs->exp_type == TEMP && bop->rhs->exp_type == CONSTANT){
					temp = (Temp *)bop->lhs;
					cons = handle_constant(((Constant *)bop->rhs)->val);
				}else if(bop->rhs->exp_type == TEMP && bop->lhs->exp_type == CONSTANT){
					temp = (Temp *)bop->rhs;
					cons = handle_constant(((Constant *)bop->lhs)->val);
				}else{
					return false;
				}

				if(offset == cons){
					return true;
				}
			}else if(exp->exp_type == TEMP){
				Temp *temp = (Temp *)exp;
				if(temp->name == str_reg[R_ESP] && offset == 0){
					return true;
				}else{
					return false;
				}
			}else{
				return false;
			}
		}else{
			return false;
		}
	}else{
		return false;
	}

	return false;
}

/*map type from given DIE to variables in ptarget_list*/
/*exp is the Mem[] containing a pointer*/
bool check_call_pointer(Dwarf_Debug dbg, Dwarf_Die die, func_vertex_ptr func_list, int block, int stmt, Exp *exp, Graph &g){
	bool result;
	int i;
	Dwarf_Die die_type;
	Dwarf_Off off_type = 0;
	result = get_die_type(dbg, die, &die_type, &off_type);
	if(result == false){
		return false;
	}

	Dwarf_Half tag;
	result = get_die_tag(die_type, &tag);
	if(result == false){
		return false;
	}

	/*get dvar*/
	vector <location *> null_fb;
	dvariable *source = new dvariable(dbg, die, null_fb);
	dptr * var_l = new dptr(dbg, *source, die_type, off_type, 0, (dvariable *)0);

	switch(tag){
	case DW_TAG_pointer_type:{
		dvariable *var_l_base;
		if(is_single_ptr(var_l, var_l_base) == true){
			Graph::vertex_descriptor vtd = -1;
			vtd = read_exp(func_list, block, stmt, exp, g);
			if(vtd == -1){
				/*Single in function info v.s. multiple fields in accessed variable*/
				return false;
			}

			sign_type_t sut = ((dbase *)var_l_base)->original_su;
			if(sut == SIGNED_T){
				add_edge_with_cap(func_list->s_des, vtd, MAX_CAP, 0, g);
			}else if(sut == UNSIGNED_T){
				add_edge_with_cap(vtd, func_list->u_des, MAX_CAP, 0, g);
			}

			return true;
		}else{
			/*struct*/
			/*set type according to name and size*/
			vector<Pointed *> ptarget_list, pstack;
			push_lib_var(var_l, ptarget_list);
			int i, j;

			//get pointer
			dptr *ptr_dbg = 0;
			Tmp_s * tmps = 0;
			if(is_tmps(exp) == true){
				tmps = (Tmp_s *)exp;
			}

			for(i = 0; i < func_list->ptr_list.getsize(); i++){
				/*check ptr original location*/
				if(func_list->ptr_list.plist.at(i)->debug_info->cmp_loc(exp, func_list->stmt_block->block_list[block]->block[stmt]->asm_address) == true){
					/*plist.at(i) is the corresponding pointer*/
					ptr_dbg = func_list->ptr_list.plist.at(i)->debug_info;
					break;
				}

				/*check copy list*/
				if(tmps != 0){
					int j;
					for(j = 0; j < func_list->ptr_list.plist.at(i)->copy_list.size(); j++){
						result = func_list->ptr_list.plist.at(i)->copy_list.at(j)->cmp_tmp(tmps);
						if(result == true){
							ptr_dbg = func_list->ptr_list.plist.at(i)->debug_info;
							break;
						}
					}
				}

				if(ptr_dbg != 0){
					break;
				}
				}

			if(ptr_dbg == 0){
				return false;
			}

			/*put all children of ptr_dbg into pstack*/
			for(i = 0; i < func_list->ptarget_list.size(); i++){
				for(j = 0; j < func_list->ptarget_list.at(i)->debug_info_list.size(); j++){
					if(check_child(ptr_dbg, func_list->ptarget_list.at(i)->debug_info_list.at(j)) == true){
						pstack.push_back(func_list->ptarget_list.at(i));
						break;
					}
				}
			}

			/*mapping from lib info to ptargets in pstack*/
			for(i = 0; i < ptarget_list.size(); i++){
				for(j = 0; j < pstack.size(); j++){
					if(pstack.at(j)->cmp_pointed(ptarget_list.at(i)) == true){
						//Set s/u type according to ptarget_list
						sign_type_t sut = ptarget_list.at(i)->debug_info_list.at(0)->original_su;
						if(sut == SIGNED_T){
							add_edge_with_cap(func_list->s_des, pstack.at(j)->my_descriptor, MAX_CAP, 0, g);
						}else if(sut == UNSIGNED_T){
							add_edge_with_cap(pstack.at(j)->my_descriptor, func_list->u_des, MAX_CAP, 0, g);
						}
						break;
					}
				}
			}
			return true;
		}

		break;
	}
	default:{
		break;
	}
	}

	return false;
}

//whether given dptr* point to a single type (or a struct)
bool is_single_ptr(dptr *ptr, dvariable *&ret){
	dvariable * var = ptr->var;
	while(var != 0){
		switch(var->var_struct_type){
		case DVAR_BASE:{
			ret = var;
			return true;
		}
		case DVAR_ARRAY:{
			var = ((darray *)var)->var;
			break;
		}
		case DVAR_STRUCT:{
			ret = var;
			return false;
		}
		case DVAR_POINTER:{
			var = ((dptr *)var)->var;
			break;
		}
		case DVAR_UN:{
			perror("DVAR_UN");
			exit(-1);
		}

		default:{
			break;
		}
		}
	}

	return false;
}

//Similar to push_each_pointer, but this one is for pushing ret/params of lib funcs to formal structure
void push_lib_var(dvariable *var, vector<Pointed *> &ptarget_list){
	if(var == 0){
		return;
	}
	switch(var->var_struct_type){
	case DVAR_BASE:{
		dbase *base = (dbase *)var;
		//Check whether its a new pointer type
		int ptr_pos = check_ptr(var, ptarget_list);
		if(ptr_pos == -1){
			/*Add new pointer to ptr_list*/
			string name = get_full_name(base);
			Pointed *tmp = new Pointed(base, -1, name);
			ptarget_list.push_back(tmp);
		}else{
			/*This type already exist*/
			/*Add new debug_info only*/
			ptarget_list.at(ptr_pos)->Add_into_list(base);
		}

		break;
	}
	case DVAR_STRUCT:{
		dstruct * stru = (dstruct *)var;
		int i;
		if(stru->leaf == false){
			for(i = 0; i < stru->member_list.size(); i++){
				//cout<<"member_list size = "<<stru->member_list.size() << endl;
				if(stru->member_list.at(i) != 0){
					push_lib_var(stru->member_list.at(i), ptarget_list);
				}
			}
		}
		break;
	}
	case DVAR_ARRAY:{
		darray * arr = (darray *)var;
		if(arr->var != 0 && arr->leaf != true){
			push_lib_var(arr->var, ptarget_list);
		}
		break;
	}
	case DVAR_POINTER:{
		dptr * ptr = (dptr *)var;
		if(ptr->leaf == false){
			push_lib_var(ptr->var, ptarget_list);
		}
		break;
	}
	default:{
		break;
	}
	}
}
