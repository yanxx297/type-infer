#ifndef INFER_H_
#define INFER_H_



void dfs_min_cut(Graph::vertex_descriptor src, func_vertex_ptr func_block, Graph &g);
int reg_name_to_dwop(Temp * tmp);
bool check_duplicated_edge(func_vertex_ptr func_list, int src_node, int des_node, Graph &g);
void print_capacity(Graph &g);
Traits::edge_descriptor add_edge_with_cap(func_vertex_ptr func_list, Traits::vertex_descriptor &v1,
                                Traits::vertex_descriptor &v2,
                                const double capacity_fwd,
                                const double capacity_rev,
                                Graph &g);
Graph::vertex_descriptor add_default_vertex(Graph &g, sign_type_t su_type);
void print_variable_list(func_vertex_ptr *func_list, int len);
bool check_duplicate_operation(func_vertex_ptr func_block, Operation *op);
int search_by_func_name(func_vertex_ptr func_block, fblock_ptr *vine_ir_block);
bool is_var(func_vertex_ptr func_block, Graph::vertex_descriptor v_des);
int var_lookup(func_vertex_ptr func_block, Exp *exp, int block, int stmt);
bool is_flag(Tmp_s *reg_tmp);
bool push_register(func_vertex_ptr func_block, Tmp_s *reg_tmp, Graph& g);
bool search_reg(func_vertex_ptr func_list, Tmp_s *target);
int search_var(func_vertex_ptr func_list, int block, int stmt, Mem *target);
Graph::vertex_descriptor node_searcher(func_vertex_ptr func_list, int block, int stmt, Exp *target);
bool def_searcher(fblock_ptr vine_ir_block, int block_no, int stmt_no, int *block, int *stmt, Tmp_s *target, Exp *&res);
bool sf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g);
bool cf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g);
void smod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var,  Graph& g);
void handle_smod(func_vertex_ptr func_block, int descriptor, Graph& g);
void mod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var,  Graph& g);
void handle_mod(func_vertex_ptr func_block, int descriptor, Graph& g);
void handle_sar(func_vertex_ptr func_block, int descriptor, Graph& g);
void handle_shr(func_vertex_ptr func_block, int descriptor, Graph& g);
void handle_operation(func_vertex_ptr func_block, Graph& g);
void check_cjmp(fblock_ptr vine_ir_block, func_vertex_ptr func_list, Exp *cond, int block_no, int stmt_no, Graph& g);

bool compare_mem(Mem *former, Mem *latter);
bool compare_exp(Exp *former, Exp *latter);

string get_full_name(dbase *var);

Graph::vertex_descriptor read_exp(func_vertex_ptr func_block, int block, int stmt, Exp *exp, Graph& g);
bool array_loopup(fblock_ptr vine_ir_block, func_vertex_ptr func_block, int block, int stmt, Move *mov, Graph::vertex_descriptor op, Graph &g);

void check_movzsbl(func_vertex_ptr func_list, Cast *src, Temp *dst, Graph::vertex_descriptor v_src, Graph &g);
void check_call(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block, int stmt, string func_name, Graph &g);
void check_func(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block, int stmt, string func_name, Graph &g);
bool get_prev_stmt(fblock_ptr vine_ir_block, int block, int stmt, int *b, int *s);
bool check_param(Stmt *stmt, int offset);

bool get_next_stmt(fblock_ptr vine_ir_block, int block, int stmt, int *b, int *s);
bool set_edge(fblock_ptr vine_ir_block, func_vertex_ptr func_list,Dwarf_Debug dbg, Dwarf_Die param, int block, int stmt, int *new_offset, Exp *current_exp, Graph &g);
bool check_call_pointer(Dwarf_Debug dbg, Dwarf_Die die, fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block, int stmt, Exp *exp, Graph &g);
bool is_single_ptr(dptr *ptr, dvariable *&ret);
void push_lib_var(dvariable *var, vector<Pointed *> &ptarget_list);

bool get_return_value(fblock_ptr vine_ir_block, int block, int stmt, int *ret_block, int *ret_stmt, Exp *&ret);
bool get_xth_param(fblock_ptr vine_ir_block, int offset, int block, int stmt, int *ret_block, int *ret_stmt,Exp *&ret);
bool set_single_edge(func_vertex_ptr func_list, Exp *exp, int block, int stmt, sign_type_t signedness, Graph &g);
#endif /* INFER_H_ */
