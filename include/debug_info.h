#ifndef DEBUG_INFO_H_
#define DEBUG_INFO_H_


using namespace std;

//----------------------------------------------------------------------------------------X
typedef enum {
  OFFSET=0,
  ADDRESS,
}LOCTYPE;

struct offset{
	Dwarf_Off offset;//Dwarf_Unsigned
	Dwarf_Small reg_name;
};

struct pointed_type{
	Dwarf_Off offset;//identify the type of pointed area
	int offset_strucr;//Offset for structure array, -1 if not
	Dwarf_Unsigned su_type;
	string type_name;
	//Tmp_s *addr;//reg or [reg + offset]
	vector<Tmp_s *> addr_list;
	BOOL addr_set;//Whether addr has been set///////////NO USE
};

struct var_info{
	string var_name;
	Dwarf_Unsigned var_length;
	LOCTYPE loc_type;
	Dwarf_Unsigned su_type;
	union {
		Dwarf_Unsigned var_addr;
		offset var_offset;
	};
	int array_pos;//Position if in an array, -1 if not.
	//Dwarf_Die type_die;//store the type die of this variable. Store the type DIE of pointed area if this var is a pointer
	pointed_type pointed_info;
};

struct subprog{
	string subprog_name;
	vector<var_info *> variable;
};

vector<subprog> debug_info;
struct subprog global;

static void read_cu_list(Dwarf_Debug dbg);
static void print_die_data(Dwarf_Debug dbg, Dwarf_Die print_me, int level);
static void get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die,
		int in_level);
static BOOL get_var(Dwarf_Debug dbg, Dwarf_Die print_me, int level, struct var_info *&ret);

static void print_debug_info(vector<subprog> dbg);
static struct var_info *get_array_member(Dwarf_Debug dbg, Dwarf_Die print_me,
		Dwarf_Die array_info, int pos, int level);

static void handle_lexical_block(struct subprog &curr_sub, Dwarf_Debug dbg,
		Dwarf_Die lex_die, int level);
static void handle_var_die(struct subprog &curr_sub, Dwarf_Debug dbg,
		Dwarf_Die print_me, int level);

static Dwarf_Die get_type(Dwarf_Debug dbg, Dwarf_Die curr_die, Dwarf_Off *type_offset);
void set_location(Dwarf_Die var, struct var_info *&curr_var);
void set_length(Dwarf_Die die, struct var_info *&curr_var, Dwarf_Debug dbg);
Dwarf_Unsigned set_su(Dwarf_Die die);
int set_offset(Dwarf_Die var);
string set_name(Dwarf_Die die);
void get_struct_ptr(Dwarf_Debug dbg, Dwarf_Die var, Dwarf_Off type_offset, Dwarf_Die stru, Dwarf_Die member, struct var_info *&ret);


#endif /* DEBUG_INFO_H_ */
