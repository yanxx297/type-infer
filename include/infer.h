#ifndef INFER_H_
#define INFER_H_



void dfs_min_cut(Graph::vertex_descriptor src, func_vertex_ptr func_block, Graph &g);
int reg_name_to_dwop(Temp * tmp);
BOOL check_duplicated_edge(int src_node, int des_node, Graph &g);
void print_capacity(Graph &g);
Traits::edge_descriptor add_edge_with_cap(Traits::vertex_descriptor &v1,
                                Traits::vertex_descriptor &v2,
                                const double capacity_fwd,
                                const double capacity_rev,
                                Graph &g);
Graph::vertex_descriptor add_default_vertex(Graph &g, sign_type_t su_type);
void print_variable_list(func_vertex_ptr *func_list, int len);
int check_duplicate_operation(func_vertex_ptr func_block, Operation *op);
int search_by_func_name(func_vertex_ptr func_block, fblock_ptr *vine_ir_block);
BOOL is_var(func_vertex_ptr func_block, Graph::vertex_descriptor v_des);
int var_lookup(func_vertex_ptr func_block, Exp *exp, int block, int stmt);
BOOL is_flag(Tmp_s *reg_tmp);
int push_register(func_vertex_ptr func_block, Tmp_s *reg_tmp, Graph& g);
int search_reg(func_vertex_ptr func_list, Tmp_s *target);
int search_var(func_vertex_ptr func_list, int block, int stmt, Mem *target);
int search_op(func_vertex_ptr func_list, int block, int stmt, Exp *target);
Graph::vertex_descriptor node_searcher(func_vertex_ptr func_list, int block, int stmt, Exp *target);
BOOL def_searcher(fblock_ptr vine_ir_block, int block_no, int stmt_no, Tmp_s *target, Exp *&res);
BOOL sf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g);
BOOL cf_handler(fblock_ptr vine_ir_block, func_vertex_ptr func_list, int block_no, int stmt_no, Temp *exp, Graph& g);
void smod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var,  Graph& g);
void handle_smod(func_vertex_ptr func_block, int descriptor, Graph& g);
void mod_operand_handler(func_vertex_ptr func_block, Graph::vertex_descriptor operand_binop, Graph::vertex_descriptor operand_var,  Graph& g);
void handle_mod(func_vertex_ptr func_block, int descriptor, Graph& g);
void handle_sar(func_vertex_ptr func_block, int descriptor, Graph& g);
void handle_shr(func_vertex_ptr func_block, int descriptor, Graph& g);
void handle_operation(func_vertex_ptr func_block, Graph& g);
void check_cjmp(fblock_ptr vine_ir_block, func_vertex_ptr func_list, Exp *cond, int block_no, int stmt_no, Graph& g);

BOOL compare_mem(Mem *former, Mem *latter);
BOOL compare_exp(Exp *former, Exp *latter);

string get_full_name(dbase *var);

void check_movzsbl(func_vertex_ptr func_list, Cast *src, Temp *dst, Graph::vertex_descriptor v_src, Graph &g);

#endif /* INFER_H_ */
