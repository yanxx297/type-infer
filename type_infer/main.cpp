#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>

/*include Vine*/
#include "asm_program.h"
#include "disasm-pp.h"
extern "C"
{
#include "libvex.h"
}
#include "irtoir.h"

/*include BGL*/
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/breadth_first_search.hpp>

#include <boost/graph/copy.hpp>

#include <boost/graph/incremental_components.hpp>
#include <boost/pending/disjoint_sets.hpp>

#include <boost/graph/boykov_kolmogorov_max_flow.hpp>
#include <boost/graph/push_relabel_max_flow.hpp>

/*include libdwarf*/
#include "dwarf.h"
#include "libdwarf.h"

/*include elf*/
#include <gelf.h>

#include <utility>

#include "type_common.h"
#include "location.h"
#include "dvar.h"
#include "tmp_s.h"
#include "interproc.h"
#include "vine_api.h"
#include "vertex.h"
#include "infer.h"
#include "ptr_handler.h"
#include "debug_tool.h"





//#define DEBUG

using namespace std;

int func_list_len;
int func_len;
struct addr_range* text;
map <int, call_map *> call_table;

int s_s, s_u, u_s, u_u, s_un, u_un;


////////////////////////////////////////////////////////////
//	Write to dot file
////////////////////////////////////////////////////////////

//Given the descriptor of a undirected graph (undig), return the corresponding node in another directed graph.
//2 graphs are connected by func_vertex_ptr
Graph::vertex_descriptor undi_to_dig(Undirect_Graph::vertex_descriptor src, Undirect_Graph &undig, Graph &dig, func_vertex_ptr func_block){
	Graph::vertex_descriptor res;

	boost::property_map<Undirect_Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), undig);
	boost::property_map<Undirect_Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), undig);

	switch(g_vet[src]){
	case VARIABLE:{
		res = func_block->variable_list.at(g_id[src])->my_descriptor;
		break;
	}
	case REGISTER:{
		res = func_block->reg_list.at(g_id[src])->my_descriptor;
		break;
	}
	case POINTED:{
		res = func_block->ptarget_list.at(g_id[src])->my_descriptor;
		break;
	}
	case OPERATION:{
		res = func_block->op_list.at(g_id[src])->my_descriptor;
		break;
	}
	case S_NODE:{
		res = func_block->s_des;
		break;
	}
	case U_NODE:{
		res = func_block->u_des;
		break;
	}
	default:
		break;
	}

	return res;

}

//Make vertices that neither belong to signed/unsigned components or are variables invisible
//Removing vertex won't change descripters in edges, that's why I merely marked it as invisible rather than delete it
void remove_unrelated_nodes(func_vertex_ptr func_block, Undirect_Graph& g, Graph &dig, boost::disjoint_sets<Rank, Parent>& ds){
	boost::property_map<Graph, visible_type_t>::type g_vi = boost::get(visible_type_t(), dig);
	boost::property_map<Undirect_Graph, vertex_exp_type_t>::type ug_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, dig);
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), dig);
	pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	if(ds.find_set(*vp.first) != ds.find_set(func_block->s_des) &&
    			ds.find_set(*vp.first) != ds.find_set(func_block->u_des)){
    		Graph::vertex_descriptor src = undi_to_dig(*vp.first, g, dig, func_block);
    		if(ug_vet[*vp.first] != VARIABLE && ug_vet[*vp.first] != POINTED){
        		g_vi[src] = false;
        		//printf("remove node %s\n", g_name[src].c_str());
    		}
//    		else if(ug_vet[*vp.first] == VARIABLE){
//    			func_block->variable_list.at(g_id[src])->infered_su = UNKNOW_T;
//    		}else if(ug_vet[*vp.first] == POINTED){
//    			func_block->ptarget_list.at(g_id[src])->infered_su = UNKNOW_T;
//    		}
    	}
    }
}

void set_component_to_unknown(func_vertex_ptr func_block, Undirect_Graph& g, Graph &dig, boost::disjoint_sets<Rank, Parent>& ds){
	boost::property_map<Graph, visible_type_t>::type g_vi = boost::get(visible_type_t(), dig);
	boost::property_map<Undirect_Graph, vertex_exp_type_t>::type ug_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, dig);
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), dig);
	pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	if(ds.find_set(*vp.first) != ds.find_set(func_block->s_des) &&
    			ds.find_set(*vp.first) != ds.find_set(func_block->u_des)){
    		Graph::vertex_descriptor src = undi_to_dig(*vp.first, g, dig, func_block);
    		if(ug_vet[*vp.first] == VARIABLE){
    			func_block->variable_list.at(g_id[src])->infered_su = UNKNOW_T;
    		}else if(ug_vet[*vp.first] == POINTED){
    			func_block->ptarget_list.at(g_id[src])->infered_su = UNKNOW_T;
    		}
    	}
    }

}

//Set the whole component to signed
//For 2 separated components only
void set_componet_to_signed(func_vertex_ptr func_block, Undirect_Graph& g, Graph &dig, boost::disjoint_sets<Rank, Parent>& ds){
	boost::property_map<Graph, signed_unsigend_type_t>::type g_su = boost::get(signed_unsigend_type_t(), dig);
	boost::property_map<Undirect_Graph, vertex_exp_type_t>::type ug_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), dig);
	pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	if(ds.find_set(*vp.first) == ds.find_set(func_block->s_des)){

    		Graph::vertex_descriptor src = undi_to_dig(*vp.first, g, dig, func_block);
    		g_su[src] = SIGNED_T;
    		if(ug_vet[src] == VARIABLE){
    			func_block->variable_list.at(g_id[src])->infered_su = SIGNED_T;
    		}else if(ug_vet[src] == POINTED){
    			func_block->ptarget_list.at(g_id[src])->infered_su = SIGNED_T;
    		}
    	}
    }
}

void print_component(Undirect_Graph::vertex_descriptor &node, func_vertex_ptr func_block, Undirect_Graph& g, Graph &dig, boost::disjoint_sets<Rank, Parent>& ds){
	boost::property_map<Graph, visible_type_t>::type g_vi = boost::get(visible_type_t(), dig);
	pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	Graph::vertex_descriptor node_d = undi_to_dig(*vp.first, g, dig, func_block);
    	if(ds.find_set(*vp.first) != ds.find_set(node)){
    		g_vi[node_d] = true;
    	}else{
    		g_vi[node_d] = false;
    	}
    }
}

//Print out the infered signed/unsigned type of a single graph
void print_type_infer_result(func_vertex_ptr func_block, const char *progname){
	FILE *fp = 0;
	int i;
	int ss =0;
	int sun = 0;
	int su = 0;
	int us = 0;
	int uun = 0;
	int uu = 0;
	for(i = 0; i < func_block->variable_list.size(); i++){
		if(func_block->variable_list.at(i)->infered_su == SIGNED_T){
			printf("\t%s: Signed\\",get_full_name(func_block->variable_list.at(i)->debug_info).c_str());
		}else if(func_block->variable_list.at(i)->infered_su == UNSIGNED_T){
			printf("\t%s: Unsigned\\",get_full_name(func_block->variable_list.at(i)->debug_info).c_str());
		}else{
			printf("\t%s: Unknow\\",get_full_name(func_block->variable_list.at(i)->debug_info).c_str());
		}

		if(func_block->variable_list.at(i)->debug_info->original_su == SIGNED_T){
			printf("Signed\n");
		}else if(func_block->variable_list.at(i)->debug_info->original_su == UNSIGNED_T){
			printf("Unsigned\n");
		}else{
			printf("Unknow\n");
		}

		sign_type_t original = func_block->variable_list.at(i)->debug_info->original_su;
		sign_type_t infer = func_block->variable_list.at(i)->infered_su;
		if(original == infer){
			if(original == SIGNED_T){
				ss++;
				fp = fopen(SS,"a");
				if(fp != NULL){
					fprintf(fp,"%s %s %s\n", func_block->variable_list.at(i)->var_name.c_str(), func_block->func_name.c_str(), progname);
				}
				fclose(fp);
			}else if(original == UNSIGNED_T){
				uu++;
				fp = fopen(UU,"a");
				if(fp != NULL){
					fprintf(fp,"%s %s %s\n", func_block->variable_list.at(i)->var_name.c_str(), func_block->func_name.c_str(), progname);
				}
				fclose(fp);
			}
		}else{
			if(original == SIGNED_T){
				if(infer == UNSIGNED_T){
					su++;
					fp = fopen(SU,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->variable_list.at(i)->var_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
				}else if(infer == UNKNOW_T){
					sun++;
					fp = fopen(SNK,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->variable_list.at(i)->var_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
				}
			}else if(original == UNSIGNED_T){
				if(infer == SIGNED_T){
					us++;
					fp = fopen(US,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->variable_list.at(i)->var_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
				}else if(infer == UNKNOW_T){
					uun++;
					fp = fopen(UNK,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->variable_list.at(i)->var_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
				}
			}
		}

	}

	for(i = 0; i < func_block->ptarget_list.size(); i++){
		if(func_block->ptarget_list.at(i)->infered_su == SIGNED_T){
			printf("\t%s: Signed\\",get_full_name(func_block->ptarget_list.at(i)->debug_info_list.at(0)).c_str());
		}else if(func_block->ptarget_list.at(i)->infered_su == UNSIGNED_T){
			printf("\t%s: Unsigned\\",get_full_name(func_block->ptarget_list.at(i)->debug_info_list.at(0)).c_str());
		}else{
			printf("\t%s: Unknow\\",get_full_name(func_block->ptarget_list.at(i)->debug_info_list.at(0)).c_str());
		}
		if(func_block->ptarget_list.at(i)->debug_info_list.at(0)->original_su == SIGNED_T){
			printf("Signed\n");
		}else if(func_block->ptarget_list.at(i)->debug_info_list.at(0)->original_su == UNSIGNED_T){
			printf("Unsigned\n");
		}else{
			printf("Unknow\n");
		}

		sign_type_t original = func_block->ptarget_list.at(i)->debug_info_list.at(0)->original_su;
		sign_type_t infer = func_block->ptarget_list.at(i)->infered_su;
		if(original == infer){
			if(original == SIGNED_T){
				ss++;
				fp = fopen(SS,"a");
				if(fp != NULL){
					fprintf(fp,"%s %s %s\n", func_block->ptarget_list.at(i)->ptr_name.c_str(), func_block->func_name.c_str(), progname);
				}
				fclose(fp);
			}else if(original == UNSIGNED_T){
				uu++;
				fp = fopen(UU,"a");
				if(fp != NULL){
					fprintf(fp,"%s %s %s\n", func_block->ptarget_list.at(i)->ptr_name.c_str(), func_block->func_name.c_str(), progname);
				}
				fclose(fp);
			}
		}else{
			if(original == SIGNED_T){
				if(infer == UNSIGNED_T){
					su++;
					fp = fopen(SU,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->ptarget_list.at(i)->ptr_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
				}else if(infer == UNKNOW_T){
					fp = fopen(SNK,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->ptarget_list.at(i)->ptr_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
					sun++;
				}
			}else if(original == UNSIGNED_T){
				if(infer == SIGNED_T){
					us++;
					fp = fopen(US,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->ptarget_list.at(i)->ptr_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
				}else if(infer == UNKNOW_T){
					uun++;
					fp = fopen(UNK,"a");
					if(fp != NULL){
						fprintf(fp,"%s %s %s\n", func_block->ptarget_list.at(i)->ptr_name.c_str(), func_block->func_name.c_str(), progname);
					}
					fclose(fp);
				}
			}
		}
	}

	s_s += ss;
	u_s += us;
	u_u += uu;
	s_u += su;
	s_un += sun;
	u_un += uun;

	/*print matrix*/
	cout<<"signed->signed:"<<dec<<ss<<endl;
	cout<<"unsigned->unsigned:"<<dec<<uu<<endl;
	cout<<"signed->unsigned:"<<dec<<su<<endl;
	cout<<"unsigned->signed:"<<dec<<us<<endl;
	cout<<"signed->unknow:"<<dec<<sun<<endl;
	cout<<"unsigned->unknow:"<<dec<<uun<<endl;
}

void draw_var_graph(func_vertex_ptr func_block, Graph& g){
	FILE *fp;
	int i;

	boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
	boost::property_map<Graph, boost::vertex_color_t>::type g_color = boost::get(boost::vertex_color, g);
	boost::property_map<Graph, signed_unsigend_type_t>::type g_sut = boost::get(signed_unsigend_type_t(), g);
	boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
	boost::property_map<Graph, visible_type_t>::type g_vi = boost::get(visible_type_t(), g);



	char filename[256];
	strcpy(filename, func_block->func_name.c_str());
	strcat(filename, "_dig");

	if((fp = fopen(filename, "w")) == NULL){
		print_error("Fail to creat file/folder");
		exit(1);
	}
	fprintf(fp, "digraph G {\n");

//	Draw vertices
    pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(g); vp.first != vp.second; ++vp.first){
    	//fprintf(fp, "%d [label=\"%s\" vis:%d vet:%d];\n",*vp.first,g_name[*vp.first].c_str(),g_vi[*vp.first], g_vet[*vp.first]);
    	if(g_vi[*vp.first] == true){
        	if(g_vet[*vp.first] == S_NODE){
        		fprintf(fp, "%d [label=\"%s\", color=\"brown2\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
        	}else if(g_vet[*vp.first] == U_NODE){
        		fprintf(fp, "%d [label=\"%s\", color=\"deepskyblue1\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
        	}else if(g_vet[*vp.first] == VARIABLE){
        		sign_type_t su_type = func_block->variable_list.at(g_id[*vp.first])->debug_info->original_su;
    			if(su_type == SIGNED_T){
    				fprintf(fp, "%d [label=\"%s\", color=\"orange\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
    			}else if(su_type == UNSIGNED_T){
    				fprintf(fp, "%d [label=\"%s\", color=\"green1\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
    			}

        	}else if( g_vet[*vp.first] == POINTED){
        		sign_type_t su_type = func_block->ptarget_list.at(g_id[*vp.first])->debug_info_list.at(0)->original_su;
    			if(su_type == SIGNED_T){
    				fprintf(fp, "%d [label=\"%s\", color=\"orange\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
    			}else if(su_type == UNSIGNED_T){
    				fprintf(fp, "%d [label=\"%s\", color=\"green1\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
    			}

        	}else if(g_vet[*vp.first] == REGISTER || g_vet[*vp.first] == OPERATION){
        		if(g_sut[*vp.first] == SIGNED_T){
        			fprintf(fp, "%d [label=\"%s\", color=\"pink1\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
        		}else if(g_sut[*vp.first] == UNSIGNED_T){
        			fprintf(fp, "%d [label=\"%s\", color=\"lightblue\", style=\"filled\"];\n",*vp.first,g_name[*vp.first].c_str());
        		}
        	}else{

        		fprintf(fp, "%d [label=\"%s\"];\n",*vp.first,g_name[*vp.first].c_str());
        	}
    	}
    }

//    Draw egdes
	  boost::property_map<Graph, boost::edge_capacity_t>::type capacity = boost::get(boost::edge_capacity, g);
	  boost::property_map < Graph, visedge_type_t >::type g_evis = boost::get(visedge_type_t(), g);

    boost::graph_traits<Graph>::edge_iterator ei, ei_end;
        for (tie(ei, ei_end) = boost::edges(g); ei != ei_end; ++ei){
    	if(capacity[*ei] >0 &&
    			g_evis[*ei] == true &&
    			g_vi[source(*ei, g)] == true &&
    			g_vi[target(*ei, g)] == true){
    		fprintf(fp,"%d -> %d;\n",source(*ei, g), target(*ei, g));
    	}
    }

	fprintf(fp, "}\n");
	fclose(fp);
}

/*Push var into ptarget list*/
void push_each_pointer(dvariable *var, func_vertex_ptr &func_list, Graph& g){
	if(var == 0){
		return;
	}
	switch(var->var_struct_type){
	case DVAR_BASE:{
		boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
		boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
		boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);
		dbase *base = (dbase *)var;
		//Check whether its a new pointer type
		int ptr_pos = check_ptr(var, func_list->ptarget_list);
		if(ptr_pos == -1){
			/*Add new pointer to ptr_list*/
			Graph::vertex_descriptor v_ptr;
			v_ptr = add_default_vertex(g, UNSIGNED_T);

			string name = get_full_name(base);
			Pointed *tmp = new Pointed(base,v_ptr, name);
			//tmp->Add_into_list(debug_info.at(pos).variable.at(j));
			func_list->ptarget_list.push_back(tmp);
			cout<<"push pointer "<<tmp->debug_info_list.at(0)->var_name<<" as g["<<v_ptr<<"]"<<endl;

			g_id[v_ptr] = func_list->ptarget_list.size() - 1;
			g_vet[v_ptr] = POINTED;
			g_name[v_ptr] = name;
		}else{
			/*This type already exist*/
			/*Add new debug_info only*/
			func_list->ptarget_list.at(ptr_pos)->Add_into_list(base);
		}

		break;
	}
	case DVAR_STRUCT:{
		dstruct * stru = (dstruct *)var;
		int i;
		if(stru->leaf != true){
			for(i = 0; i < stru->member_list.size(); i++){
				if(stru->member_list.at(i) != 0){
					push_each_pointer(stru->member_list.at(i), func_list, g);
				}
			}
		}
		break;
	}
	case DVAR_ARRAY:{
		darray * arr = (darray *)var;
		if(arr->var != 0 && arr->leaf != true){
			push_each_pointer(arr->var, func_list, g);
		}
		break;
	}
	case DVAR_POINTER:{
		dptr * ptr = (dptr *)var;
		bool res_add = func_list->ptr_list.add_pointer(ptr);
		if(ptr->var != 0 && ptr->leaf != true && res_add == true){
			//Only continue adding child if this pointer is not duplicate
			push_each_pointer(ptr->var, func_list, g);
		}
		break;
	}
	default:{
		break;
	}
	}
}

void push_each_var(dvariable *var, func_vertex_ptr func_list, Graph& g){
	switch(var->var_struct_type){
	case DVAR_BASE:{
		boost::property_map<Graph, identity_in_list_type_t>::type g_id = boost::get(identity_in_list_type_t(), g);
		boost::property_map<Graph, boost::vertex_name_t>::type g_name = boost::get(boost::vertex_name, g);
		boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(vertex_exp_type_t(), g);

		Graph::vertex_descriptor v_reg;
		dbase *base = (dbase *)var;
		if(base->original_su == SIGNED_T || base->original_su == UNSIGNED_T){
			v_reg = add_default_vertex(g, base->original_su);
		}else{
			//base->print_me();
			cout<<"Unknown type of variable, stop."<<endl;
			break;
		}

		string name = get_full_name(base);

		Variable *tmp = new Variable(base,v_reg,name);
		func_list->variable_list.push_back(tmp);
		cout<<"push variable "<<tmp->debug_info->var_name<<" as g["<<v_reg<<"]"<<endl;

		g_id[v_reg] = func_list->variable_list.size() - 1;
		g_vet[v_reg] = VARIABLE;
		g_name[v_reg] = name;
		break;
	}
	case DVAR_STRUCT:{
		cout<<"check struct: "<<var->var_name<<endl;
		dstruct * stru = (dstruct *)var;
		if(stru->leaf != true){
			int i;
			for(i = 0; i < stru->member_list.size(); i++){
				if(stru->member_list.at(i) != 0){
					push_each_var(stru->member_list.at(i), func_list, g);
				}
			}
		}
		break;
	}
	case DVAR_ARRAY:{
		cout<<"check arr: "<<var->var_name<<endl;
		darray * arr = (darray *)var;
		if(arr->var != 0 && arr->leaf != true){
			push_each_var(arr->var, func_list, g);
		}
		break;
	}
	case DVAR_POINTER:{
		cout<<"check ptr: "<<var->var_name<<endl;
		dptr * ptr = (dptr *)var;
		if(ptr->var != 0){
			push_each_pointer(ptr,func_list,g);
//			if(ptr->leaf != YES){
//				push_each_var(ptr->var, func_list, g);
//			}
		}
//		if(ptr->var != 0 && ptr->leaf != YES){
//			push_each_var(ptr->var, func_list, g);
//		}else if(ptr->var != 0 && ptr->leaf == YES){
//			push_each_pointer(ptr,func_list,g);
//		}
		break;
	}
	default:{
		break;
	}
	}
}


//For each function of debug info (other than the first block of structure, global)
//Add variables to a vector
void push_variable(subprogram *prog, func_vertex_ptr func_list, Graph& g){
	int j;

	func_list->func_name = prog->name;
	for(j = 0; j < prog->var_list.size(); j++){
		dvariable *var = prog->var_list.at(j);
		if(var->var_struct_type != DVAR_POINTER){
			push_each_var(var, func_list, g);
		}else{
			push_each_pointer(var, func_list, g);
		}
	}


}

//block and stmt are for func_list
void visit_exp(fblock_ptr vine_ir_block, func_vertex_ptr func_list, Graph& g){
	int i, j, k;
	boost::property_map < Graph, boost::edge_reverse_t >::type rev = boost::get(boost::edge_reverse, g);

	//This function can be found in source code
	//read ever Exp in this function, add register and operation into func_list[pos]
	for(j = 0; j < vine_ir_block->len; j++){
		for(k = 0; k <vine_ir_block->block_list[j]->blen; k++){
			//read Exp recursively
			switch(vine_ir_block->block_list[j]->block[k]->stmt_type){
			case JMP:{
				read_exp(func_list, j, k, ((Jmp *)vine_ir_block->block_list[j]->block[k])->target, g);
				break;
			}
			case CJMP:{
				//Look for <, <=, >, >= and add edges to signed/unsigend node
				check_cjmp(vine_ir_block, func_list, ((CJmp *)vine_ir_block->block_list[j]->block[k])->cond, j, k, g);

				read_exp(func_list, j, k, ((CJmp *)vine_ir_block->block_list[j]->block[k])->t_target, g);
				read_exp(func_list, j, k, ((CJmp *)vine_ir_block->block_list[j]->block[k])->f_target, g);
				break;
			}
			case SPECIAL:{
				Special *t_special = (Special *)vine_ir_block->block_list[j]->block[k];
				if(t_special->special == "call"){
					//Can be dynamic or static
					//Currently ignore static. Will enable static in future, and uses addr range to distinguish

					//For dynamic: map to a function string accroding to the jmp before this stmt
					//Then read mem[esp+cons] = ... before this stmt
					Jmp *call_addr = NULL;
					if(k < 1){
						if(vine_ir_block->block_list[j-1]->block[vine_ir_block->block_list[j-1]->blen-1]->stmt_type == JMP){
							call_addr = (Jmp *)vine_ir_block->block_list[j-1]->block[vine_ir_block->block_list[j-1]->blen-1];
						}
					}else{
						if(vine_ir_block->block_list[j]->block[k-1]->stmt_type == JMP){
							call_addr = (Jmp *)vine_ir_block->block_list[j-1]->block[vine_ir_block->block_list[j-1]->blen-1];
						}
					}
					if(call_addr != NULL){
						if(call_addr->target->exp_type == NAME){
							string target_name = ((Name *) call_addr->target)->name;
							if(target_name.substr(0,5) == "pc_0x"){
								Elf64_Addr addr = name_to_hex(target_name);
								map <int, call_map *>::iterator it;
								for(it = call_table.begin(); it != call_table.end(); it ++){
									if(it->second->addr == addr){
										string str = it->second->func_name;
										cout<<"######call "<<str<<endl;
										check_call(vine_ir_block, func_list, j, k, str, g);
									}
								}
							}
						}
					}

				}
				break;
			}
			case MOVE:{
				//check whether this MOVE is an access of pointers
				get_ptr_copy(func_list, ((Move *)vine_ir_block->block_list[j]->block[k]), j, k);

				//Check variable with offset(s)
				Graph::vertex_descriptor v_l;// = boost::add_vertex(g);
				Graph::vertex_descriptor v_r;// = boost::add_vertex(g);
				v_l = read_exp(func_list, j, k, ((Move *)vine_ir_block->block_list[j]->block[k])->lhs, g);
				v_r = read_exp(func_list, j, k, ((Move *)vine_ir_block->block_list[j]->block[k])->rhs, g);

				if(v_l == -1 || v_r == -1){
					//NOTE: T will return a -1
					if(v_l == -1 && v_r != -1 &&
							((Move *)vine_ir_block->block_list[j]->block[k])->lhs->exp_type == TEMP &&
							((Move *)vine_ir_block->block_list[j]->block[k])->rhs->exp_type == CAST){
						//Check movzbl/movsbl
						Temp *dst = ((Temp *)((Move *)vine_ir_block->block_list[j]->block[k])->lhs);
						Cast *src = ((Cast *)((Move *)vine_ir_block->block_list[j]->block[k])->rhs);
						check_movzsbl(func_list, src, dst, v_r, g);
					}else{
						//do nothing
					}
					break;
				}

				add_edge_with_cap(v_r,v_l, 1, 1, g);
				break;
			}
			case COMMENT:{
				//No Exp
				break;
			}
			case LABEL:{
				//No Exp
				break;
			}
			case EXPSTMT:{
				read_exp(func_list, j, k, ((ExpStmt *)vine_ir_block->block_list[j]->block[k])->exp, g);
				break;
			}
			case VARDECL:{
				//No Exp
				break;
			}
			case CALL:{
				//Doesn't exist?
				read_exp(func_list, j, k, ((Call *)vine_ir_block->block_list[j]->block[k])->callee, g);
				read_exp(func_list, j, k, ((Call *)vine_ir_block->block_list[j]->block[k])->lval_opt, g);
				int w;
				for(w = 0; w < ((Call *)vine_ir_block->block_list[j]->block[k])->params.size(); w++){
					read_exp(func_list, j, k, ((Call *)vine_ir_block->block_list[j]->block[k])->params.at(w), g);
				}
				break;
			}
			case RETURN:{
				read_exp(func_list, j, k, ((Return *)vine_ir_block->block_list[j]->block[k])->exp_opt, g);
				break;
			}
			case FUNCTION:{
				//No Exp, but have Stmt and vardel
				break;
			}
			case ASSERT:{
				read_exp(func_list, j, k, ((Assert *)vine_ir_block->block_list[j]->block[k])->cond, g);
				break;
			}
			default:
				break;
			}
		}
	}

}

void handle_function(vector<vine_block_t *> &vine_blocks, asm_program_t * prog, program * dinfo, int func_num, bool ssaf, bool rmvf){
	int i, j, k;
	fblock_ptr tmp;
	tmp = transform_to_ssa(vine_blocks, prog, func_num, text);
	if(tmp->len == 0){
		//cout<<"Empty function block"<<endl;
		return;
	}
	printf("SSA tranformation of Vine IR ----OK\n");

	//Replace all Temp variables on the right side
	tmp = tranform_to_tmp_free(tmp, func_num);

	printf("Tmp free version of Vine IR ----OK\n");

	printf("***********************handle function[%d] %s***********************\n", func_num, tmp->func->name.c_str());

	if (ssaf == true) {
		//    Write ssa version of vine ir into another file
		FILE *ssair;
		char filename[256];
		strcpy(filename, tmp->func->name.c_str());
		strcat(filename, "_ssa.txt");
		if ((ssair = fopen(filename, "w")) == NULL) {
			print_error("Fail to creat file/folder");
			exit(1);
		}

		fprintf(ssair,
				"***********************function <%s>%d start***********************\n",
				tmp->func->name.c_str(), func_num);
		for (j = 0; j < tmp->len; j++) {
			fprintf(ssair, "BB_%d{\n", j);
			printf("BB_%d{\n", j);
			for (k = 0; k < tmp->block_list[j]->blen; k++) {
				fprintf(ssair, "\t%x",
						tmp->block_list[j]->block[k]->asm_address);
				printf("\t%x", tmp->block_list[j]->block[k]->asm_address);
				fprintf(ssair, "\t%s\n",
						tmp->block_list[j]->block[k]->tostring().c_str());
				printf("\t%s\n",
						tmp->block_list[j]->block[k]->tostring().c_str());
			}
			fprintf(ssair, "}\n");
			printf("}\n");
		}
		fprintf(ssair,
				"***********************function <%s>%d end***********************\n",
				tmp->func->name.c_str(), func_num);
	}

	//    Deal with debug info
	//

	func_vertex_ptr func_list = new struct func_vertex_block();


	//    Initialize variable list
	//


	Graph g;

	for(i = 0; i < dinfo->func_list.size(); i++){
		if(dinfo->func_list.at(i)->name == tmp->func->name){
			break;
		}
	}

	if(i >= dinfo->func_list.size()){
		return;
	}

	func_list->stmt_block = tmp;
	push_variable(dinfo->func_list.at(i), func_list, g);

	boost::property_map<Graph, boost::vertex_name_t>::type g_name =
			boost::get(boost::vertex_name, g);
	boost::property_map<Graph, vertex_exp_type_t>::type g_vet = boost::get(
			vertex_exp_type_t(), g);

	//Add signed & unsigned node to each graph
	Graph::vertex_descriptor v_signed = add_default_vertex(g, SIGNED_T);
	//boost::add_vertex(g);
	Graph::vertex_descriptor v_unsigned = add_default_vertex(g, UNSIGNED_T);
	//boost::add_vertex(g);
	g_name[v_signed] = "Signed";
	g_vet[v_signed] = S_NODE;
	g_name[v_unsigned] = "Unsigned";
	g_vet[v_unsigned] = U_NODE;

	func_list->u_des = v_unsigned;
	func_list->s_des = v_signed;

	//print pointers
	func_list->ptr_list.print_plist();


	visit_exp(tmp, func_list, g);


	printf("Basic Graph ----OK\n");

	//    handle signed/unsigned operations by traveling through graph
	//    !!Comparison already handled while parsing vine ir
	handle_operation(func_list, g);

	printf("Signed / unsigend operation analysing ----OK\n");

	Undirect_Graph new_graph;
	boost::copy_graph(g, new_graph);

	//    Compute connected components
	vector<vertex_index_udi> rank(boost::num_vertices(new_graph));
	vector<vertex_iter_udi> parent(boost::num_vertices(new_graph));
	boost::disjoint_sets<Rank, Parent> ds(&rank[0], &parent[0]);
	boost::initialize_incremental_components(new_graph, ds);
	boost::incremental_components(new_graph, ds);

	//   	    "Remove" extra vertices
	if(rmvf == true){
		remove_unrelated_nodes(func_list, new_graph, g, ds);
	}

	//Set componets that neither contains SIGNED nor UNSIGNED vertice to UNKNOWN_T
	set_component_to_unknown(func_list, new_graph, g, ds);

	//   	    Handle different situations
	//   	    compute minimum cut if there is more than one component
	if (ds.find_set(func_list->s_des)
			== ds.find_set(func_list->u_des)) {
		printf("Signed and unsigend are in the same component: %d\n",
				ds.find_set(func_list->s_des));

		//   	    	Compute max flow
		EdgeWeightType flow = boost::boykov_kolmogorov_max_flow(
				g, func_list->s_des, func_list->u_des);
		//EdgeWeightType flow = boost::push_relabel_max_flow(graph_list.at(i), func_list[i]->s_des, func_list[i]->u_des);
		printf("The max flow is: %d\n", flow);

		//   	    	Compute minimum cut
		dfs_min_cut(func_list->s_des, func_list, g);

		//   	    	Reset visited property
		reset_visited(g);

		//   	    	Set only nodes on paths from i to unsigned visible

#ifdef DEBUG
		look_for_binop(func_list[i], 87, XOR, graph_list.at(i));
		printf("\n");
		look_for_binop_by_des(func_list[i], func_list[i]->variable_list.at(1)->my_descriptor, XOR, graph_list.at(i));
#endif

		//id_to_vineir(func_list, g);

	} else {
		//Coloring every node in signed component to red(signed)
		set_componet_to_signed(func_list, new_graph, g, ds);
	}


//	Apply debug tools
//	Traits::vertex_descriptor src = 2;
//	print_path(src, func_list->u_des, g);
//	End of debug tools

	//Display pointed info
	func_list->ptr_list.print_copylists();
	//draw_var_undigraph(func_list[i], new_graph, ds);

	printf("Draw graph[%d] <%s>\n", func_num, func_list->func_name.c_str());
	draw_var_graph(func_list, g);

	printf("***********************Finished handle function[%d] %s***********************\n", func_num, tmp->func->name.c_str());

	//    Print out infer result
	printf(
			"***********************infer result*******************************\n");
	printf("%s:\n", func_list->func_name.c_str());
	print_type_infer_result(func_list, prog->abfd->filename);
}

int
main(int argc, char **argv)
{

    Dwarf_Debug dbg = 0;
    int fd = -1;
    char *filepath = "<stdin>";
    int res = DW_DLV_ERROR;
    Dwarf_Error error;
    Dwarf_Handler errhand = 0;
    Dwarf_Ptr errarg = 0;
    int count = 0;

    s_s = 0;
    s_u = 0;
    u_s = 0;
    u_u = 0;
    s_un = 0;
    u_un = 0;

    int i, j, k;


    filepath = argv[1];

    //---------------------------------------------------------------------------------X
    //ELF file header
    text = new struct addr_range();
    get_call_table(filepath, call_table, text);
	map <int, call_map *>::iterator it;
	for(it = call_table.begin(); it != call_table.end(); it ++){
		cout<<"#"<<it->first<<":"<<hex<<it->second->addr<<" "<<it->second->func_name<<endl;
	}

    fd = open(filepath,O_RDONLY);
    if(fd < 0) {
        printf("Failure attempting to open \"%s\"\n",filepath);
    }

    //---------------------------------------------------------------------------------X
    //debug info
    res = dwarf_init(fd,DW_DLC_READ,errhand,errarg, &dbg,&error);
    if(res != DW_DLV_OK) {
        printf("Giving up, cannot do DWARF processing\n");
        exit(1);
    }

	program * prog = new program(dbg);
	prog->print_program();
    res = dwarf_finish(dbg,&error);
    if(res != DW_DLV_OK) {
        printf("dwarf_finish failed!\n");
    }
    close(fd);

    //----------------------------------------------------------------------------------X
    //vine IR
    vector<vine_block_t *> vine_blocks;
    asm_program_t * asmprog;
    trans_to_vineir(argv[1], vine_blocks, asmprog);
    int func_num = -1;
    bool ssaf_flag = false;
    bool rmv_flag = false;

    for(count = 0; count < argc; count++){
    	if(strcmp(argv[count], "-single")==0 && (count+1)<argc){
    		func_num = atoi(argv[count+1]);
    		break;
    	}
    }

    for(count = 0; count < argc; count++){
    	if(strcmp(argv[count], "-ssaf")==0){
    		ssaf_flag = true;
    		break;
    	}
    }

    for(count = 0; count < argc; count++){
    	if(strcmp(argv[count], "-rmv")==0){
    		rmv_flag = true;
    		break;
    	}
    }

    if(func_num == -1){
    	/*handle all functions*/
    	int vineIR_func_num = vine_blocks.size();
    	for(i = 0; i < vineIR_func_num; i++){
    		handle_function(vine_blocks, asmprog, prog, i, ssaf_flag, rmv_flag);
    	}

    }else{
    	/*handle a signle function*/
    	handle_function(vine_blocks, asmprog, prog, func_num, ssaf_flag, rmv_flag);
    }



		// print overall inference result
	cout
			<< "***********************overall result*******************************"
			<< endl;
	cout << "signed->signed:" << dec << s_s << endl;
	cout << "unsigned->unsigned:" << dec << u_u << endl;
	cout << "signed->unsigned:" << dec << s_u << endl;
	cout << "unsigned->signed:" << dec << u_s << endl;
	cout << "signed->unknown:" << dec << s_un << endl;
	cout << "unsigned->unknown:" << dec << u_un << endl;

    return 0;
}
