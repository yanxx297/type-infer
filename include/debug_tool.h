void reset_visited(Graph &g);
void reset_visible(Graph &g);
bool print_node(Graph::vertex_descriptor current_node,Graph::vertex_descriptor des, Graph &g);
void print_path(Traits::vertex_descriptor &src, Traits::vertex_descriptor &des, Graph &g);
void look_for_binop(func_vertex_ptr func_block, int index, binop_type_t op, Graph &g);
void look_for_binop_by_des(func_vertex_ptr func_block, Graph::vertex_descriptor des, binop_type_t op, Graph &g);
void id_to_vineir(func_vertex_ptr func_block, Graph &g);

void print_ptargetlist(vector<Pointed *> &list);
void print_reg(func_vertex_ptr func_block);
