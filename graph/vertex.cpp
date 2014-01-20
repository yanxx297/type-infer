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

/*include libdwarf*/
#include "dwarf.h"
#include "libdwarf.h"

#include "type_common.h"
#include "location.h"
#include "dvar.h"
#include "tmp_s.h"
#include "vine_api.h"
#include "vertex.h"

vertex::vertex(vertex_type_t vertex_type, Graph::vertex_descriptor descriptor)
:vertex_type(vertex_type), my_descriptor(descriptor)
{}

Variable::Variable(dbase *debug_info, Graph::vertex_descriptor descriptor, string name)
:vertex(VARIABLE,descriptor),debug_info(debug_info), var_name(name), infered_su(UNSIGNED_T)
{}

Pointed::Pointed(dbase *debug_info, Graph::vertex_descriptor descriptor, string name)
:vertex(POINTED,descriptor), ptr_name(name), infered_su(UNSIGNED_T)
{
	//this->debug_info_list.push_back(debug_info);
	//this->id_oddset = debug_info->pointed_info.offset;
	//this->struct_offset = debug_info->pointed_info.offset_strucr;
	this->Add_into_list(debug_info);
}

void Pointed::Add_into_list(dbase *debug_info){
	if(this->debug_info_list.size() == 0){
		this->debug_info_list.push_back(debug_info);
	}else{
		if(this->debug_info_list.at(0)->cmp_type(debug_info) == YES){
			this->debug_info_list.push_back(debug_info);
		}else{
			perror("This pointer is invalid for this type, cannot push");
		}
	}
}

BOOL Pointed::cmp_ptr_type(dvariable * ptr){
	BOOL result = NO;
	if(this->debug_info_list.at(0)->cmp_type(ptr) == YES){
		result = YES;
	}
	return result;
}

Register::Register(Exp *reg_info,Graph::vertex_descriptor descriptor)
:vertex(REGISTER,descriptor),reg_info(reg_info)
{}

Operation::Operation(op_type_t op_type, Graph::vertex_descriptor descriptor, int block, int stmt)
:vertex(OPERATION,descriptor),op_type(op_type), block_number(block), stmt_number(stmt)
{};

Bin_Operation::Bin_Operation(binop_type_t t,Graph::vertex_descriptor l, Graph::vertex_descriptor r, Graph::vertex_descriptor descriptor, BinOp *exp, int block, int stmt)
:Operation(BIN_OP, descriptor, block, stmt), binop_type(t), operand_l(l), operand_r(r), exp(exp)
{};

Un_Operation::Un_Operation(unop_type_t t, Graph::vertex_descriptor op, Graph::vertex_descriptor descriptor, int block, int stmt)
:Operation(UN_OP, descriptor, block, stmt), unop_type(t), operand(op)
{};

//----------------------------------------------------------------------------------------------------------------X
//Pointer class(es)

pointer_info::pointer_info(dptr *debug_info)
:debug_info(debug_info)
{}

string pointer_info::tostring(){
	string res;
	int i;

	res = this->debug_info->var_name +":";
	for(i = 0; i < this->child_list.size(); i++){
		res += this->child_list.at(i)->debug_info->var_name + ",";
	}

	return res;
}

void pointer_info::print_copylist(){
	int i;
	cout<<this->debug_info->var_name<<":"<<endl;
	for(i = 0; i < this->copy_list.size(); i++){
		cout<<"\t"<<this->copy_list.at(i)->tostring()<<endl;
	}
}

pointer_list::pointer_list(){}

void pointer_list::add_pointer(dptr *debug_info){
	int i;
	pointer_info *p_info = new pointer_info(debug_info);
	for(i = 0; i < this->plist.size(); i++){
		if(check_child(p_info->debug_info, this->plist.at(i)->debug_info) == YES){
			/*this is a parent of plist[i]*/
			/*add plist[i] to this.list*/
			p_info->child_list.push_back(this->plist.at(i));
		}else if(check_child(this->plist.at(i)->debug_info, p_info->debug_info) == YES){
			/*this is a child of plist[i]*/
			/*add this to plist[i].list*/
			this->plist.at(i)->child_list.push_back(p_info);
		}
	}
	this->plist.push_back(p_info);
}

void pointer_list::print_plist(){
	int i;
	for(i = 0; i < this->plist.size(); i++){
		cout<<this->plist.at(i)->tostring()<<endl;
	}
}

int pointer_list::getsize(){
	return (this->plist.size());
}

void pointer_list::print_copylists(){
	int i;
	for(i = 0; i < this->getsize(); i++){
		this->plist.at(i)->print_copylist();
		cout<<"***********************************"<<endl;
	}
}

//----------------------------------------------------------------------------------------------------------------X
//Common utils

//check whether var_c is a child of var_p in debug_info structure
BOOL check_child(dvariable *var_p, dvariable *var_c){
	BOOL res = NO;

	//c->p
	dvariable *buf = var_c;
	while(buf != 0){
		buf = buf->parent;
		if(buf == var_p){
			res = YES;
			break;
		}
	}

	return res;
}

BOOL check_child_from_parent(dvariable *var_p, dvariable *var_c){
	//p->c

	BOOL res = NO;
	if(var_p == 0){
		return res;
	}

	if(var_p == var_c){
		res = YES;
		return res;
	}

	DVAR_TYPE_T ptype = var_p->var_struct_type;
	switch(ptype){
	case DVAR_ARRAY:{
		darray *buf = (darray *)var_p;
		if(buf->leaf != YES){
			res = check_child_from_parent(buf->var, var_c);
		}
		break;
	}
	case DVAR_STRUCT:{
		int i;
		dstruct *buf = (dstruct *)var_p;
		for(i = 0; i < buf->member_list.size(); i++){
			if(buf->member_list.at(i)->leaf != YES){
				res = check_child_from_parent(buf->member_list.at(i), var_c);
			}
		}
		break;
	}
	case DVAR_POINTER:{
		dptr *buf = (dptr *)var_p;
		if(buf->leaf != YES){
			res = check_child_from_parent(buf->var, var_c);
		}
		break;
	}
	default:{
		break;
	}
	}
}

