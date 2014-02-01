#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>
#include <utility>

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
//#include "debug_info.h"
#include "vertex.h"

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
	g_visited[src] = YES;

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
    	if(source(*ei, g) == src && g_visited[target(*ei, g)]!= YES){
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
BOOL check_duplicated_edge(int src_node, int des_node, Graph &g){
	BOOL result = NO;

    boost::graph_traits<Graph>::edge_iterator ei, ei_end;
    for (tie(ei, ei_end) = boost::edges(g); ei != ei_end; ++ei){
    	if(source(*ei, g) == src_node &&
    			target(*ei, g) == des_node){
    		result = YES;
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
	if(check_duplicated_edge(v1, v2, g) == NO &&
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
		  g_evis[e1] = YES;
		  g_evis[e2] = NO;
	}
}

Graph::vertex_descriptor add_default_vertex(Graph &g, sign_type_t su_type){
	Graph::vertex_descriptor vtx = boost::add_vertex(g);

//	Set default property of the vertex
	boost::property_map<Graph, signed_unsigend_type_t>::type g_su = boost::get(signed_unsigend_type_t(), g);
	boost::property_map<Graph, visible_type_t>::type g_vi = boost::get(visible_type_t(), g);

	g_su[vtx] = su_type;
	g_vi[vtx] = YES;
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
							if(compare_exp(((Bin_Operation *)op)->exp->lhs,((Bin_Operation *)func_block->op_list.at(i))->exp->lhs) == NO){
								flag = 1;
							}
						}
						if(((Bin_Operation *)op)->operand_r == -1){
							if(compare_exp(((Bin_Operation *)op)->exp->rhs,((Bin_Operation *)func_block->op_list.at(i))->exp->rhs) == NO){
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
BOOL is_var(func_vertex_ptr func_block, Graph::vertex_descriptor v_des){
	BOOL res = NO;
	int i;
	for(i = 0; i < func_block->variable_list.size(); i++){
		if(func_block->variable_list.at(i)->my_descriptor == v_des){
			res = YES;
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
				if(dvar->cmp_loc(exp, func_block->stmt_block->block_list[block]->block[stmt]->asm_address) == YES){
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
BOOL is_flag(Tmp_s *reg_tmp){
	BOOL res = NO;
	int i;
	if(reg_tmp->name == str_reg[EFLAGS]){
		res = YES;
	}else{
		for(i = R_CF; i <= R_ACFLAG; i++){
			if(reg_tmp->name == str_reg[i]){
				res = YES;
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
	if(is_flag(reg_tmp)==NO){
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
BOOL def_searcher(fblock_ptr vine_ir_block, int block_no, int stmt_no, Tmp_s *target, Exp *&res){
	int i, j;
	BOOL result = NO;
	for(i = block_no; i>0; i--){
		for(j = (i == block_no? stmt_no: (vine_ir_block->block_list[i]->blen-1)); j > 0; j--){
			if(vine_ir_block->block_list[i]->block[j]->stmt_type == MOVE){
				if(((Move *)vine_ir_block->block_list[i]->block[j])->lhs->exp_type == TEMP){
					if(get_reg_position(((Temp *)((Move *)vine_ir_block->block_list[i]->block[j])->lhs)->name) != -1){
						if(((Tmp_s *)(Temp *)((Move *)vine_ir_block->block_list[i]->block[j])->lhs)->index == target->index ||
								((Tmp_s *)(Temp *)((Move *)vine_ir_block->block_list[i]->block[j])->lhs)->name == target->name){
							res = ((Move *)vine_ir_block->block_list[i]->block[j])->rhs;
							result = YES;
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
BOOL sf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g){
	Exp *def;
	BOOL result = NO;
	Graph::vertex_descriptor opr_l = -1;
	Graph::vertex_descriptor opr_r = -1;
	if(get_reg_position(exp->name) == -1){
		return result;
	}else{
		if(def_searcher(vine_ir_block, block_no, stmt_no, ((Tmp_s *)exp), def) == NO){
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
					result = YES;
					break;
				}else{
					if((((BinOp *)tmp)->lhs->exp_type == BINOP && ((BinOp *)tmp)->rhs->exp_type == BINOP)||
							(((BinOp *)tmp)->lhs->exp_type != BINOP && ((BinOp *)tmp)->rhs->exp_type != BINOP)){
						result = NO;
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
BOOL cf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g){
	Exp *def;
	BOOL result = NO;
	Graph::vertex_descriptor opr_l = -1;
	Graph::vertex_descriptor opr_r = -1;
	if(get_reg_position(exp->name) == -1){
		return result;
	}else{
		if(def_searcher(vine_ir_block, block_no, stmt_no, ((Tmp_s *)exp), def) == NO){
			return result;
		}else{
			//Now the defination of CF is in def
			//Get the Exp = a < b
			Exp *tmp = def;
			printf("cf_handler: %s\n",tmp->tostring().c_str());
			while(tmp->exp_type == BINOP){
				if(((BinOp *)tmp)->binop_type == LT){
					//tmp = a < b
					result = YES;
					break;
				}else{
					if((((BinOp *)tmp)->lhs->exp_type == BINOP && ((BinOp *)tmp)->rhs->exp_type == BINOP)||
							(((BinOp *)tmp)->lhs->exp_type != BINOP && ((BinOp *)tmp)->rhs->exp_type != BINOP)){
						result = NO;
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
		if(is_tmps(tmp_mv->lhs) == YES){
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

BOOL compare_mem(Mem *former, Mem *latter){
	//Check whether the 2 Mem* represent the same location
	BOOL result = NO;
	if(former->addr->exp_type != latter->addr->exp_type){
		result = NO;
	}else{
		if(former->addr->exp_type == BINOP){
			if(((BinOp *)former->addr)->lhs->exp_type == TEMP &&
					((BinOp *)former->addr)->rhs->exp_type == CONSTANT &&
					((BinOp *)latter->addr)->lhs->exp_type == TEMP &&
					((BinOp *)latter->addr)->rhs->exp_type == CONSTANT){
				if(((Tmp_s *)((BinOp *)former->addr)->lhs)->index == ((Tmp_s *)((BinOp *)latter->addr)->lhs)->index &&
						((Constant *)((BinOp *)former->addr)->rhs)->val == ((Constant *)((BinOp *)latter->addr)->rhs)->val){
					result = YES;
				}
			}
		}else if(former->addr->exp_type == TEMP){
			if(get_reg_position(((Temp *)former->addr)->name) != -1 &&
					get_reg_position(((Temp *)latter->addr)->name) != -1 ){
				if(((Tmp_s *)former->addr)->index == ((Tmp_s *)latter->addr)->index){
					result = YES;
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
BOOL compare_exp(Exp *former, Exp *latter){
	BOOL result = NO;
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
				result = YES;
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
