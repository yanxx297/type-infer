#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>

#include "asm_program.h"
#include "disasm-pp.h"

extern "C"
{
#include "libvex.h"
}
#include <cassert>
#include "irtoir.h"

#include "type_common.h"
#include "tmp_s.h"
#include "vine_api.h"



using namespace std;


// ------------------------------------------------------------
// Class Tmp_s
//         temp + id numebr
// ------------------------------------------------------------
Tmp_s::Tmp_s(Temp *tmp, int id) :
		Temp(tmp->typ, tmp->name) , index(id) {
}

Tmp_s::Tmp_s(reg_t typ, string name, int id) :
	Temp(typ, name), index(id){
}

string Tmp_s::tostring() const {
	//printf("Call Tmp_s.tostring()\n");
	char ssa_id[64];
	sprintf(ssa_id,"%d",index);
	string id(ssa_id);
	return name + "_" + id + ":" + Exp::string_type(typ);
}

void Tmp_s::destroy(Tmp_s *expr) {
	assert(expr);
	delete expr;
}

Tmp_s *
Tmp_s::clone() const
{
  return new Tmp_s(*this);
}

// ------------------------------------------------------------
// Class Phi_s
//         Phi functions that take tmp_s as parameter
// ------------------------------------------------------------


Phi_s::Phi_s(string orig_name, vector<Tmp_s*> v)
  : Exp(PHI), vars(v), phi_name(orig_name)
{
}

Phi_s *
Phi_s::clone() const
{
  return new Phi_s(*this);
}

string
Phi_s::tostring() const
{
  string ret = "PHI(";
  string comma = " ";
  for (vector<Tmp_s *>::const_iterator it = vars.begin();
       it != vars.end(); it++) {
    ret += comma;
    ret += (*it)->tostring();
    comma = ",";
  }
  ret += " )";
  return ret;
}

void Phi_s::addVar(Tmp_s* e){
	vars.push_back(e);
}

int Phi_s::check_duplicate_para(int dup){
	int result = 0;
	int i;
	for(i = 0; i < vars.size(); i++){
		if(vars.at(i)->index == dup){
			result = 1;
			break;
		}
	}
	return result;
}

void Phi_s::destroy( Phi_s *expr )
{
    assert(expr);

    unsigned int i;

    for ( i = 0; i < expr->vars.size(); i++ )
    {
        Exp::destroy(expr->vars.at(i));
    }

    delete expr;
}

//check whether a Exp is a Tmp_s
BOOL is_tmps(Exp *input){
	BOOL res = NO;
	if(input->exp_type == TEMP){
		Temp *tmp = (Temp *)input;
		if(get_reg_position(tmp->name) != -1){
			res = YES;
		}
	}

	return res;
}
