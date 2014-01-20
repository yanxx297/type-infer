#ifndef DWARF_UTIL
#define DWARF_UTIL



using namespace std;
dvariable* check_loop_type(dvariable *var, Dwarf_Off type_offset);
BOOL get_frame_base(Dwarf_Die die, vector<location *> &loc_list);
BOOL check_artificial(Dwarf_Die die);

BOOL get_die_name(Dwarf_Die die, string &ret);
BOOL get_die_type(Dwarf_Debug dbg, Dwarf_Die die, Dwarf_Die *ret, Dwarf_Off *ret_off);
BOOL get_die_loclist(Dwarf_Die die, vector<location *> &loc_list, vector<location *> &frame_base);

BOOL get_die_size(Dwarf_Die typeDie, int *ret);
BOOL get_die_offset(Dwarf_Die typeDie, int *ret);
BOOL get_array_size(Dwarf_Die typeDie, int *ret);
BOOL get_die_su(Dwarf_Die typeDie, sign_type_t *ret);

BOOL get_die_tag(Dwarf_Die die, Dwarf_Half *tag);
Dwarf_Small handle_dwop(Dwarf_Small input, int number);
void erase_locrecord(address_t highpc, address_t lowpc, vector<location *> &input);

void customize_loclist(dvariable *var);
void handle_child_and_sibling(Dwarf_Debug dbg, Dwarf_Die in_die, vector<dvariable *> &var_list, vector<location *> &frame_base);

BOOL cmp_offset_loc(string regname, int offset, address_t pc, dvariable *var);
BOOL cmp_offset(int in_offset, dvariable *var);
int handle_constant(unsigned long long offset);

#endif
