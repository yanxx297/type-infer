#ifndef INTERPROC_H_
#define INTERPROC_H_

using namespace std;

struct call_map{
	Elf64_Addr addr;
	string func_name;
};

struct addr_range{
	Elf64_Addr low_addr;
	Elf64_Addr high_addr;
};





//-------------------------------------------------------------------------------------X
//For the next three functions: elf must be set back to begin before used again
void get_relplt(Elf *elf, size_t shstrndx, map <int, call_map *> &call_table);

void get_dynsym(Elf *elf, size_t shstrndx, map <int, call_map *> &call_table);

void get_sec_range(Elf *elf, char *sec_name, size_t shstrndx, Elf64_Addr *low_addr, Elf64_Addr *high_addr);

//-------------------------------------------------------------------------------------X
void get_call_table(char *filename, map <int, call_map *> &call_table, struct addr_range * text);


#endif /* INTERPROC_H_ */
