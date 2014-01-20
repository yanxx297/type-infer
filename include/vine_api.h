/*



Vine is Copyright (C) 2006-2009, BitBlaze Team.

You can redistribute and modify it under the terms of the GNU GPL,
version 2 or later, but it is made available WITHOUT ANY WARRANTY.
See the top-level README file for more details.

For more information about Vine and other BitBlaze software, see our
web site at: http://bitblaze.cs.berkeley.edu/
*/


#ifndef _VINE_API_H
#define _VINE_API_H


#define REGMAX 35
#define PC_RANGE 4294967295

using namespace std;

enum reg_name_t{
	R_EAX = 0,
	R_ECX,
	R_EDX,
	R_EBX,
	R_ESP,
	R_EBP,
	R_ESI,
	R_EDI,
	R_EIP,
	EFLAGS,
	R_CS,
	R_SS,
	R_DS,
	R_ES,
	R_FS,
	R_GS,
	R_CF,
	R_PF,
	R_AF,
	R_ZF,
	R_SF,
	R_OF,
	R_CC_OP,
	R_CC_DEP1,
	R_CC_DEP2,
	R_CC_NDEP,
	R_DFLAG,
	R_IDFLAG,
	R_ACFLAG,
	R_EMWARN,
	R_LDT,
	R_GDT,
	R_FTOP,
	R_FPROUND,
	R_FC3210,
};

static string str_reg[REGMAX] = {
		"R_EAX",
		"R_ECX",
		"R_EDX",
		"R_EBX",
		"R_ESP",
		"R_EBP",
		"R_ESI",
		"R_EDI",
		"R_EIP",
		"EFLAGS",
		"R_CS",
		"R_SS",
		"R_DS",
		"R_ES",
		"R_FS",
		"R_GS",
		"R_CF",
		"R_PF",
		"R_AF",
		"R_ZF",
		"R_SF",
		"R_OF",
		"R_CC_OP",
		"R_CC_DEP1",
		"R_CC_DEP2",
		"R_CC_NDEP",
		"R_DFLAG",
		"R_IDFLAG",
		"R_ACFLAG",
		"R_EMWARN",
		"R_LDT",
		"R_GDT",
		"R_FTOP",
		"R_FPROUND",
		"R_FC3210",
};

/*for 2 Exps of cjmp*/
typedef enum{
	C_T = 20,
	C_F,
}TARGET;

/*for Exps of Exp*/
typedef enum{
	LEXP = 30,
	REXP,
	EXP,
	CAST_EXP,
	ADDR,
	M_L,
	M_R,
	T_T,
	T_F,
	T_C,
	T_EXP,
	NO_OPT,
}EXP_OPT;

typedef enum{
	UNKNOW = 0 ,
	UN,
	BIN,
}BRACH;

typedef enum{
	ENTRY = 10,
	EXIT,
	INDI,
	BLOCK,
	ERROR,
}TYPE;



struct basic_block {
	Stmt **block;
	int blen; // Number of stmts in this basic block
	BRACH branch_type;
	TYPE type;
	int child_next;/*default child if there is only one children for this node*/
	int child_jmp;
	asm_function_t *func;
};

typedef struct basic_block* bblock_ptr;

struct func_block{
	bblock_ptr *block_list;
	int len; //Number of basic blocks in this function
	asm_function_t *func;
};

struct idom{
	BOOL processed;
	BOOL current_loop_processed;
	int idom_id;
};

typedef struct func_block* fblock_ptr;

static struct idom *doms;

//static int cfg_funclist_length;

extern int cfg_funclist_length;
static int global_counter;
static int current_number[REGMAX];

void to_basic_block(vector<vine_block_t *> vine_blocks, fblock_ptr func_block, address_t end);
void build_cfg(fblock_ptr func_block);
int search_lable(fblock_ptr func_block,string lable);
int get_blen(vector<vine_block_t *> vine_blocks, int i, int j, int end);
int count_block(vector<vine_block_t *> vine_blocks, int begin, int end);
int get_size(stmt_type_t type);
void print_error(string msg);
void add_edge_jmp(fblock_ptr func_block, Exp *target, int id);
void add_edge_cjmp(fblock_ptr func_block, Exp *target, int id, TARGET opt);
void print_edges(fblock_ptr func_block);
string print_nodename(struct basic_block ** nodelist, int i);
asm_function_t * get_func_name(asm_program_t *prog, vector<vine_block_t *> vine_blocks, int id);
void renew_tmp(fblock_ptr func_block);
void switch_to_tmps(Exp *parent, Exp *exp, EXP_OPT opt);
void comment_stmt(fblock_ptr vine_blocks, int i, int j);
void add_comment_jmp(fblock_ptr vine_blocks, int i, int j, Exp *target);
void add_comment(fblock_ptr vine_blocks);
void add_comment_jmp_inside(fblock_ptr func_block, int j, int k, Exp *target);
void comment_stmt_inside(fblock_ptr func_block, int j, int k);
int predecessor_num_lookup(fblock_ptr func_block, int index);

void add_phi(fblock_ptr func_block);
int intersect(struct idom *doms, int b1, int b2);
int get_predecessor(fblock_ptr func_block, struct idom *doms, int begin, int target);

void prune_cfg(fblock_ptr func_block);
void remove_bblock(fblock_ptr func_block, int target);

BOOL check_duplicated_phi(fblock_ptr func_block, int block, string name);
void insert_stmt(fblock_ptr func_block, int block, int pos, Stmt *insert);

void set_value(fblock_ptr func_block);
void set_exp_value(Exp *exp);

void set_phi_para(fblock_ptr func_block);
int search_latest_assign(fblock_ptr func_block, int target, int reg_num, Stmt *func);
int get_latest_from_bblock(fblock_ptr func_block, int block, int reg_num);
int get_normal_predecessor(fblock_ptr func_block, int begin, int target);

int get_reg_position(string reg_name);

/*Draw by graphviz*/
void draw_edges(FILE *fp, struct basic_block ** nodelist, int length);
void draw_box(FILE *fp, struct basic_block ** nodelist, int index);
void draw_graph(fblock_ptr func_block, int length);

fblock_ptr transform_to_ssa(vector<vine_block_t *> vine_blocks, asm_program_t * prog, int func_num);

BOOL check_tmp(Temp * tmp);
fblock_ptr tranform_to_tmp_free(fblock_ptr func_blocks, int func_num);
Exp *query_value(fblock_ptr func_block, int block_num, int stmt_num, Temp* t_name);
void visit_tmp(Exp *parent, Exp *exp, EXP_OPT opt, int block_num, int curr_pos, fblock_ptr func_block);

BOOL check_stmt_type(stmt_type_t type);

int search_raw_blocks(fblock_ptr vine_blocks, string label, int current);
int search_single_block_for_label(fblock_ptr vine_blocks, int block, string lable);

void remove_dom(fblock_ptr func_block, int target);

BOOL trans_to_vineir(char *filename, vector<vine_block_t *> &vine_blocks, asm_program_t * &asmprog);
#endif


