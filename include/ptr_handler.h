int check_ptr(dvariable * ptr, vector<Pointed *> &ptarget_list);
int ptarget_lookup(func_vertex_ptr func_block, Mem *exp, int block, int stmt);
int copy_from_reg_lookup(func_vertex_ptr func_block, int block, int stmt, Mem *exp);
void get_ptr_copy(func_vertex_ptr func_block, Move *exp, int block, int stmt);
int check_reg_for_offset(Exp *equal, Tmp_s *exp);
int check_plist(dptr *ptr, vector<pointer_info *> plist);

