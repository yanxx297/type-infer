#ifndef DWARF_UTIL
#define DWARF_UTIL

using namespace std;
dvariable* check_loop_type(dvariable *var, Dwarf_Off type_offset);
bool get_frame_base(Dwarf_Debug dbg, Dwarf_Die die, vector<location *> &loc_list);
bool check_artificial(Dwarf_Die die);

bool get_file_list(Dwarf_Debug dbg, Dwarf_Die die, map<int, string> &src_list);
bool get_die_file_number(Dwarf_Die typeDie, unsigned *ret);

bool get_die_name(Dwarf_Debug dbg, Dwarf_Die die, string &ret);
bool get_die_type(Dwarf_Debug dbg, Dwarf_Die die, Dwarf_Die *ret, Dwarf_Off *ret_off);
bool get_die_loclist(Dwarf_Debug dbg, Dwarf_Die die, vector<location *> &loc_list, vector<location *> &frame_base);

bool get_die_size(Dwarf_Die typeDie, int *ret);
bool get_die_offset(Dwarf_Debug dbg, Dwarf_Die typeDie, int *ret);
bool get_array_size(Dwarf_Die typeDie, int *ret);
bool get_die_su(Dwarf_Die typeDie, sign_type_t *ret);

bool get_die_tag(Dwarf_Die die, Dwarf_Half *tag);
Dwarf_Small handle_dwop(Dwarf_Small input, int number);
void erase_locrecord(address_t highpc, address_t lowpc, vector<location *> &input);

void customize_loclist(dvariable *var);
void handle_child_and_sibling(Dwarf_Debug dbg, Dwarf_Die in_die, vector<dvariable *> &var_list, map<int, string> src_list, vector<location *> &frame_base);

bool cmp_offset_loc(string regname, int offset, address_t pc, dvariable *var);
bool cmp_offset(int in_offset, dvariable *var);
int handle_constant(unsigned long long offset);

bool get_original_type(Dwarf_Debug dbg, Dwarf_Die die, Dwarf_Die *ret);
bool get_length(Dwarf_Debug dbg, Dwarf_Die die, int *ret);

int calc_len(dvariable *dvar);
void check_union_fields(dvariable *dvar, int offset, map<int, set<dbase *> > &field_list);
void handle_union_member(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, map<int, string> src_list, vector<dvariable *> &var_list);
dstruct *handle_union(Dwarf_Debug dbg, dvariable &source, Dwarf_Die die_type, Dwarf_Off off_type, int member_loc, map<int, string> src_list, dvariable *parent);

#endif
