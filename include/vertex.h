#ifndef NODE_H_
#define NODE_H_

#define MAX_CAP 65535


using namespace std;


enum vertex_type_t{
	VARIABLE,
	REGISTER,
	OPERATION,
	POINTED,
	S_NODE,
	U_NODE,
};

enum op_type_t {
	BIN_OP = 0,
	UN_OP,
};

struct signed_unsigend_type_t {
  typedef boost::vertex_property_tag kind;
};

struct vertex_exp_type_t {
  typedef boost::vertex_property_tag kind;
};

struct identity_in_list_type_t {
  typedef boost::vertex_property_tag kind;
};

struct visited_type_t {
  typedef boost::vertex_property_tag kind;
};

struct visible_type_t {
  typedef boost::vertex_property_tag kind;
};

struct visedge_type_t {
  typedef boost::edge_property_tag kind;
};

typedef int EdgeWeightType;
typedef boost::adjacency_list_traits < boost::vecS, boost::vecS, boost::directedS> Traits;
typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS,
		boost::property < boost::vertex_name_t, std::string,
		boost::property < boost::vertex_index_t, long,
		boost:: property < boost::vertex_color_t, boost::default_color_type,
		boost::property < boost::vertex_distance_t, long,
		boost::property < boost::vertex_predecessor_t, Traits::edge_descriptor,
		boost::property < signed_unsigend_type_t, sign_type_t,
		boost::property < vertex_exp_type_t, vertex_type_t,
		boost::property < identity_in_list_type_t, int,
		boost::property < visited_type_t, bool,
		boost::property < visible_type_t, bool > > > > > > > > > >,

		boost::property < boost::edge_capacity_t, EdgeWeightType,
		boost::property < boost::edge_residual_capacity_t, EdgeWeightType,
		boost::property < boost::edge_reverse_t, Traits::edge_descriptor,
		boost::property < visedge_type_t, bool > > > > > Graph;
typedef boost::graph_traits<Graph>::vertex_iterator vertex_iter;

typedef boost::adjacency_list_traits < boost::vecS, boost::vecS, boost::undirectedS> U_Traits;
typedef boost::adjacency_list <boost::vecS, boost::vecS, boost::undirectedS,
		boost::property < boost::vertex_name_t, std::string,
		boost::property < boost::vertex_index_t, long,
		boost:: property < boost::vertex_color_t, boost::default_color_type,
		boost::property < boost::vertex_distance_t, long,
		boost::property < boost::vertex_predecessor_t, Traits::edge_descriptor,
		boost::property < signed_unsigend_type_t, sign_type_t,
		boost::property < vertex_exp_type_t, vertex_type_t,
		boost::property < identity_in_list_type_t, int,
		boost::property < visited_type_t, bool,
		boost::property < visible_type_t, bool >  > > > > > > > > > > Undirect_Graph;

typedef boost::graph_traits<Undirect_Graph>::vertex_descriptor vertex_iter_udi;
typedef boost::graph_traits<Undirect_Graph>::vertices_size_type vertex_index_udi;
typedef vertex_index_udi* Rank;
typedef vertex_iter_udi* Parent;


class vertex{
public:
	vertex(vertex_type_t vertex_type, Graph::vertex_descriptor descriptor);
	vertex_type_t vertex_type;
	Graph::vertex_descriptor my_descriptor;
};

class Variable: public vertex{
public:
	Variable(dbase *debug_info, Graph::vertex_descriptor descriptor, string name);
	dbase *debug_info;
	string var_name;
	sign_type_t infered_su;
};

class Pointed: public vertex{
public:
	Pointed(dbase *debug_info, Graph::vertex_descriptor descriptor, string name);
	void Add_into_list(dbase *debug_info);
	bool cmp_ptr_type(dvariable * ptr);

	vector <dbase *> debug_info_list;
	string ptr_name;
	sign_type_t infered_su;
};

class Register: public vertex{
public:
	Register(Exp *reg_info, Graph::vertex_descriptor descriptor);
	Exp *reg_info;
};

class Operation: public vertex{
public:
	Operation(op_type_t op_type, Graph::vertex_descriptor descriptor, int block, int stmt);
	op_type_t op_type;
	int block_number;
	int stmt_number;
};

class Bin_Operation: public Operation{
public:
	Bin_Operation(binop_type_t t,Graph::vertex_descriptor l, Graph::vertex_descriptor r, Graph::vertex_descriptor descriptor, BinOp *exp, int block, int stmt);
	binop_type_t binop_type;
	Graph::vertex_descriptor operand_l;
	Graph::vertex_descriptor operand_r;
	BinOp *exp;
};

class Un_Operation: public Operation{
public:
	Un_Operation(unop_type_t t, Graph::vertex_descriptor op, Graph::vertex_descriptor descriptor, int block, int stmt);
	unop_type_t unop_type;
	Graph::vertex_descriptor operand;
};

//---------------------------------------------------------------------------------------------------------------X
//classes that will not node in graph
class pointer_info{
public:
	pointer_info(dptr *debug_info);
	string tostring();
	void print_copylist();

	dptr *debug_info;
	vector<Tmp_s *> copy_list;
	vector<pointer_info *> child_list;
};

class pointer_list{
public:
	pointer_list();
	bool add_pointer(dptr *debug_info);
	void print_plist();
	int getsize();
	void print_copylists();

	vector<pointer_info *> plist;
};


///////////////////////////////////////////////
//List of 3 kinds of vertex
//variable, register and operation
///////////////////////////////////////////////


//Three lists for each function
struct func_vertex_block{
	//asm_function_t *func;
	string func_name;
	vector<Variable *> variable_list;
	vector<Register *> reg_list;
	vector<Operation *> op_list;
	vector<Pointed *> ptarget_list;
	pointer_list ptr_list;
	Graph::vertex_descriptor s_des;
	Graph::vertex_descriptor u_des;
	fblock_ptr stmt_block;
};

typedef func_vertex_block * func_vertex_ptr;

//void print_variable_list(func_vertex_ptr *func_list, int len);
//void push_variable(subprogram *prog, func_vertex_ptr func_list, Graph& g);
//int search_by_func_name(func_vertex_ptr func_block, fblock_ptr *vine_ir_block);
//int push_register(func_vertex_ptr func_block, Tmp_s *reg_tmp, Graph& g);
//Graph::vertex_descriptor read_exp(func_vertex_ptr func_block, Exp *exp, Graph& g, boost::property_map < Graph, boost::edge_reverse_t >::type& rev);
//void visit_exp(fblock_ptr vine_ir_block, func_vertex_ptr func_list, Graph& g, boost::property_map < Graph, boost::edge_reverse_t >::type& rev);
//
//int search_op(func_vertex_ptr func_list, int block, int stmt, Exp *target);
//int search_reg(func_vertex_ptr func_list, Tmp_s *target);

bool check_child(dvariable *var_p, dvariable *var_c);
bool check_child_from_parent(dvariable *var_p, dvariable *var_c);

#endif /* NODE_H_ */

