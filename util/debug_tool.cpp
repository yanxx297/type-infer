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
#include "ptr_handler.h"
#include "debug_tool.h"

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//	Tools used to figure out and fix bugs
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//Reset the visited property of all nodes in g to NO
void reset_visited(Graph &g){
	boost::property_map<Graph, visited_type_t>::type g_visited = boost::get(visited_type_t(), g);

    pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	g_visited[*vp.first] = false;
    }
}

//Reset the visible property of all nodes in g to NO
void reset_visible(Graph &g){
	boost::property_map<Graph, visible_type_t>::type g_vis = boost::get(visible_type_t(), g);

    pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	g_vis[*vp.first] = false;
    }
}

//check each node in DFS approach
//if this node / any child tree of this node include the destination node, print this node, and return true back
bool print_node(Graph::vertex_descriptor current_node,Graph::vertex_descriptor des, Graph &g){
	bool flag = false;//flag = yes if any child tree include des
	boost::property_map<Graph, visited_type_t>::type g_visited = boost::get(visited_type_t(), g);
	boost::property_map<Graph, visible_type_t>::type g_vis = boost::get(visible_type_t(), g);

	g_visited[current_node] = true;

	//	walk through children, recursively
	    boost::graph_traits<Graph>::edge_iterator ei, ei_end;

	    if(current_node == des){
	    	g_vis[current_node] = true;
	    	flag = true;
	    }else{
		    for (tie(ei, ei_end) = boost::edges(g); ei != ei_end; ++ei){
		    	if(source(*ei, g) == current_node && g_visited[target(*ei, g)]!= true){
		    		bool res = print_node(target(*ei, g), des, g);
		    		if(res == true){
		    			flag = true;
		    		}
		    	}
		    }

		    if(flag == true){
		    	g_vis[current_node] = true;
		    }
	    }

	    return flag;
}

//Print out each path between the 2 given vertices
void print_path(Traits::vertex_descriptor &src, Traits::vertex_descriptor &des, Graph &g){
	//set all nodes invisible
	reset_visible(g);

	//DFS the whole graph
	print_node(src, des, g);
}

//look for specific operation on a specific register
void look_for_binop(func_vertex_ptr func_block, int index, binop_type_t op, Graph &g){
	boost::property_map<Graph, id_index_type_t>::type g_id = boost::get(id_index_type_t(), g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_type = boost::get(vertex_exp_type_t(), g);
	map<Exp *, Operation *>::iterator it;
	for(it = func_block->op_list.begin(); it != func_block->op_list.end(); ++it){
		if(it->second->op_type == BIN_OP){
			Bin_Operation * binop = (Bin_Operation *)it->second;
			if(binop->binop_type == op){
				if(g_type[binop->operand_l] == REGISTER){
					if(((Tmp_s *)func_block->reg_list.at(g_id[binop->operand_l])->exp)->index == index){
						printf("\t%s \n",binop->exp->tostring().c_str());
					}
				}else if(g_type[binop->operand_r] == REGISTER){
					if(((Tmp_s *)func_block->reg_list.at(g_id[binop->operand_r])->exp)->index == index){
						printf("\t%s \n",binop->exp->tostring().c_str());
					}
				}

			}
		}
	}
}

//look for operation on a specific node
void look_for_binop_by_des(func_vertex_ptr func_block, Graph::vertex_descriptor des, binop_type_t op, Graph &g){
	map<Exp *, Operation *>::iterator it;
	for(it = func_block->op_list.begin(); it != func_block->op_list.end(); ++it){
		if(it->second->op_type == BIN_OP){
			Bin_Operation * binop = (Bin_Operation *)it->second;
			if(binop->binop_type == op){
				if(binop->operand_l == des ||
						binop->operand_r == des){
					printf("\t%s \n",binop->exp->tostring().c_str());
				}
			}
		}
	}
}

//print the relationship between node numeber and corresponding vine ir to a file
void id_to_vineir(func_vertex_ptr func_block, Graph &g){
	char filename[256];
	strcpy(filename, func_block->func_name.c_str());
	strcat(filename, "_id2vineir.txt");

	FILE *fp = fopen(filename, "w");
	if(fp == NULL){
		exit(1);
	}

	map<Exp *, Operation *>::iterator it;
	for(it = func_block->op_list.begin(); it != func_block->op_list.end(); ++it){
		if(it->second->op_type == BIN_OP){
			Bin_Operation * binop = (Bin_Operation *)it->second;
			fprintf(fp, "%d\t%s\n",binop->my_descriptor, binop->exp->tostring().c_str());
		}
	}

	fclose(fp);
}

void print_ptargetlist(vector<Pointed *> &list){
	int i;
	cout<<"print ptarget list"<<endl;
	for(i = 0; i < list.size(); i++){
		list.at(i)->debug_info_list.at(0)->print_me();
		cout<<"parent struct:"<<list.at(i)->debug_info_list.at(0)->parent->var_name<<endl;
	}
}

void print_reg(func_vertex_ptr func_block){
	map<int, Register *>::iterator it;
	cout<<"reg list:"<<endl;
	for(it = func_block->reg_list.begin(); it != func_block->reg_list.end(); it ++){
		cout <<hex<<it->first<<":"<<it->second->exp->tostring()<<endl;
	}
}
