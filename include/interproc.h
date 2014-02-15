#ifndef INTERPROC_H_
#define INTERPROC_H_


struct call_map{
	Elf64_Addr addr;
	char *func_name;
};

using namespace std;

void get_relplt(Elf *elf, size_t shstrndx, map <int, call_map *> &call_table);

void get_dynsym(Elf *elf, size_t shstrndx, map <int, call_map *> &call_table);

Elf64_Addr get_pltbase(Elf *elf, size_t shstrndx);

void get_call_table(char *filename, map <int, call_map *> &call_table);


#endif /* INTERPROC_H_ */
