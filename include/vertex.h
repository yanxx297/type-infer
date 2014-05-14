#ifndef NODE_H_
#define NODE_H_

#define MAX_CAP 65535


using namespace std;


enum vertex_type_t{
	VARIABLE,
	POINTED,
	REGISTER,
	OPERATION,
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

struct id_pos_type_t {
  typedef boost::vertex_property_tag kind;
};

struct id_exp_type_t {
  typedef boost::vertex_property_tag kind;
};

struct id_index_type_t {
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
		boost::property < id_pos_type_t, int,	//For variable and pointer
		boost::property < id_exp_type_t, Exp *,	//For op
		boost::property < id_index_type_t, int, //For reg
		boost::property < visited_type_t, bool,
		boost::property < visible_type_t, bool > > > > > > > > > > > >,

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
		boost::property < id_pos_type_t, int,
		boost::property < id_exp_type_t, Exp *,
		boost::property < id_index_type_t, int,
		boost::property < visited_type_t, bool,
		boost::property < visible_type_t, bool >  > > > > > > > > > > > > Undirect_Graph;

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
	~Variable();
	dbase *debug_info;
	string var_name;
	sign_type_t infered_su;

	/*copy list: currently only used for array access*/
	vector<Tmp_s *> field_copy_list;
};

class Pointed: public vertex{
public:
	Pointed(dbase *debug_info, Graph::vertex_descriptor descriptor, string name);
	~Pointed();
	void Add_into_list(dbase *debug_info);
	bool cmp_ptr_type(dvariable * ptr);
	bool cmp_pointed(Pointed *ptr);

	vector <dbase *> debug_info_list;
	string ptr_name;
	sign_type_t infered_su;
};

class Register: public vertex{
public:
	Register(Exp *exp, Graph::vertex_descriptor descriptor);
	Exp *exp;
};

class Operation: public vertex{
public:
	Operation(op_type_t op_type, Graph::vertex_descriptor descriptor, Exp *exp, int block, int stmt);
	op_type_t op_type;
	int block_number;
	int stmt_number;
	Exp *exp;
};

class Bin_Operation: public Operation{
public:
	Bin_Operation(binop_type_t t,Graph::vertex_descriptor l, Graph::vertex_descriptor r, Graph::vertex_descriptor descriptor, BinOp *exp, int block, int stmt);
	binop_type_t binop_type;
	Graph::vertex_descriptor operand_l;
	Graph::vertex_descriptor operand_r;
};

class Un_Operation: public Operation{
public:
	Un_Operation(unop_type_t t, Graph::vertex_descriptor op, Graph::vertex_descriptor descriptor, UnOp *exp, int block, int stmt);
	unop_type_t unop_type;
	Graph::vertex_descriptor operand;
};

//---------------------------------------------------------------------------------------------------------------X
//classes that will not node in graph
class pointer_info{
public:
	pointer_info(dptr *debug_info);
	~pointer_info();
	string tostring();
	void print_copylist();

	dptr *debug_info;
	vector<Tmp_s *> copy_list;
	vector<pointer_info *> child_list;
};

class pointer_list{
public:
	pointer_list();
	void clear();
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
	vector<Pointed *> ptarget_list;

	map<int, Register *> reg_list;
	map<Exp *, Operation *> op_list;

	pointer_list ptr_list;
	Graph::vertex_descriptor s_des;
	Graph::vertex_descriptor u_des;
	fblock_ptr stmt_block;

	~func_vertex_block();
};

typedef func_vertex_block * func_vertex_ptr;


bool check_child(dvariable *var_p, dvariable *var_c);
bool check_child_from_parent(dvariable *var_p, dvariable *var_c);

#endif /* NODE_H_ */

