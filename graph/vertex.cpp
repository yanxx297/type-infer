#include <stdbool.h>

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
#include "ptr_handler.h"

vertex::vertex(vertex_type_t vertex_type, Graph::vertex_descriptor descriptor)
:vertex_type(vertex_type), my_descriptor(descriptor)
{}

Variable::Variable(dbase *debug_info, Graph::vertex_descriptor descriptor, string name)
:vertex(VARIABLE,descriptor),debug_info(debug_info), var_name(name), infered_su(UNSIGNED_T)
{}

Variable::~Variable(){
	this->field_copy_list.clear();
}

Pointed::Pointed(dbase *debug_info, Graph::vertex_descriptor descriptor, string name)
:vertex(POINTED,descriptor), ptr_name(name), infered_su(UNSIGNED_T)
{
	this->Add_into_list(debug_info);
}

Pointed::~Pointed(){
	this->debug_info_list.clear();
}

void Pointed::Add_into_list(dbase *debug_info){
	if(this->debug_info_list.size() == 0){
		this->debug_info_list.push_back(debug_info);
	}else{
		if(this->debug_info_list.at(0)->cmp_type(debug_info) == true){
			this->debug_info_list.push_back(debug_info);
		}else{
			perror("This pointer is invalid for this type, cannot push");
		}
	}
}

bool Pointed::cmp_ptr_type(dvariable * ptr){
	bool result = false;
	if(this->debug_info_list.at(0)->cmp_type(ptr) == true){
		/*Check whether in the same structure*/
		/*If yes, then not treated as the same type*/
		dvariable *myparent = this->debug_info_list.at(0)->parent;
		dvariable *parent = ptr->parent;
		if(myparent != 0 && parent != 0 && parent->cmp_type(myparent) == false){
			result = true;
		}
		result = true;
	}
	return result;
}

//Compare two ptargets based on name and size
//For check_call_pointer()
bool Pointed::cmp_pointed(Pointed *ptr){
	cout<<ptr->debug_info_list.at(0)->var_name<<"v.s."<<this->debug_info_list.at(0)->var_name<<endl;
	if(ptr->debug_info_list.at(0)->var_length != this->debug_info_list.at(0)->var_length){
		return false;
	}

	/*map by offset in a specific structure*/
	if(ptr->debug_info_list.at(0)->parent->parent != 0 &&
			this->debug_info_list.at(0)->parent->parent != 0 &&
			ptr->debug_info_list.at(0)->parent->parent->parent == 0 &&
			this->debug_info_list.at(0)->parent->parent->parent == 0){
		/*Don't check parent name if its a var name (var->ptr->struct->base), instead of a struct name*/
	}else{
		if(ptr->debug_info_list.at(0)->parent->var_name != this->debug_info_list.at(0)->parent->var_name){
			return false;
		}
	}
	if(ptr->debug_info_list.at(0)->s_offset == this->debug_info_list.at(0)->s_offset){
		return true;
	}

	return false;
}

Register::Register(Exp *exp, Graph::vertex_descriptor descriptor)
:vertex(REGISTER,descriptor),exp(exp)
{}

Operation::Operation(op_type_t op_type, Graph::vertex_descriptor descriptor, Exp *exp, int block, int stmt)
:vertex(OPERATION,descriptor),op_type(op_type), block_number(block), stmt_number(stmt), exp(exp)
{};

Bin_Operation::Bin_Operation(binop_type_t t,Graph::vertex_descriptor l, Graph::vertex_descriptor r, Graph::vertex_descriptor descriptor, BinOp *exp, int block, int stmt)
:Operation(BIN_OP, descriptor, exp, block, stmt), binop_type(t), operand_l(l), operand_r(r)
{};

Un_Operation::Un_Operation(unop_type_t t, Graph::vertex_descriptor op, Graph::vertex_descriptor descriptor, UnOp *exp, int block, int stmt)
:Operation(UN_OP, descriptor, exp, block, stmt), unop_type(t), operand(op)
{};

//----------------------------------------------------------------------------------------------------------------X
//Pointer class(es)

pointer_info::pointer_info(dptr *debug_info)
:debug_info(debug_info)
{}

pointer_info::~pointer_info(){
	this->child_list.clear();
	this->copy_list.clear();
}

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

void pointer_list::clear(){
	int i;
	for(i = 0; i < this->plist.size(); i++){
		delete this->plist.at(i);
	}
	this->plist.clear();
}

bool pointer_list::add_pointer(dptr *debug_info){
	int i;
	bool res = false;
	pointer_info *p_info = new pointer_info(debug_info);
	for(i = 0; i < this->plist.size(); i++){
		if(check_child(p_info->debug_info, this->plist.at(i)->debug_info) == true){
			/*this is a parent of plist[i]*/
			/*add plist[i] to this.list*/
			p_info->child_list.push_back(this->plist.at(i));
		}else if(check_child(this->plist.at(i)->debug_info, p_info->debug_info) == true){
			/*this is a child of plist[i]*/
			/*add this to plist[i].list*/
			this->plist.at(i)->child_list.push_back(p_info);
		}
	}

	/*Check duplicate of p_info itself*/
	if(check_plist(p_info->debug_info, this->plist) == -1){
		this->plist.push_back(p_info);
		res = true;
	}

	return res;
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

//clean a func_vertex_block struct pointed by pointer
func_vertex_block::~func_vertex_block(){
	int i;

	/*clean var list*/
	for(i = 0; i < this->variable_list.size(); i++){
		delete this->variable_list.at(i);
	}
	this->variable_list.clear();

	/*clean reg list*/
	for(map<int, Register *>::iterator it = this->reg_list.begin(); it != this->reg_list.end(); ++it){
		delete it->second;
	}
	this->reg_list.clear();

	/*clean op list*/
	for(map<Exp *, Operation *>::iterator it = this->op_list.begin(); it != this->op_list.end(); ++it){
		delete it->second;
	}
	this->op_list.clear();

	/*clean ptarget list*/
	for(i = 0; i < this->ptarget_list.size(); i++){
		delete this->ptarget_list.at(i);
	}
	this->variable_list.clear();

	/*clean (ssa form) IR list*/
	delete this->stmt_block;

	/*clean pointer list*/
	this->ptr_list.clear();

	/*clean exp->node cache*/
	this->node_list.clear();
}

//check whether var_c is a child of var_p in debug_info structure
bool check_child(dvariable *var_p, dvariable *var_c){
	bool res = false;

	//c->p
	dvariable *buf = var_c;
	while(buf != 0){
		buf = buf->parent;
		if(buf == var_p){
			res = true;
			break;
		}
	}

	return res;
}

bool check_child_from_parent(dvariable *var_p, dvariable *var_c){
	//p->c

	bool res = false;
	if(var_p == 0){
		return res;
	}

	if(var_p == var_c){
		res = true;
		return res;
	}

	DVAR_TYPE_T ptype = var_p->var_struct_type;
	switch(ptype){
	case DVAR_ARRAY:{
		darray *buf = (darray *)var_p;
		if(buf->leaf != true){
			res = check_child_from_parent(buf->var, var_c);
		}
		break;
	}
	case DVAR_STRUCT:{
		int i;
		dstruct *buf = (dstruct *)var_p;
		for(i = 0; i < buf->member_list.size(); i++){
			if(buf->member_list.at(i)->leaf != true){
				res = check_child_from_parent(buf->member_list.at(i), var_c);
			}
		}
		break;
	}
	case DVAR_POINTER:{
		dptr *buf = (dptr *)var_p;
		if(buf->leaf != true){
			res = check_child_from_parent(buf->var, var_c);
		}
		break;
	}
	default:{
		break;
	}
	}
}

