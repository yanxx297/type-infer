#include <err.h>
#include <fcntl.h>
#include <gelf.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <utility>
#include <stdbool.h>

#include <iostream>
#include <map>

#include "interproc.h"


unsigned long long int plt_base;

using namespace std;

void get_relplt(Elf *elf, size_t shstrndx, map <int, call_map *> &call_table){
	GElf_Shdr shdr;
	Elf_Scn *scn = NULL;
	GElf_Rel rel;
	char *name;
	static Elf_Data *edata; //It's important that edata is global/static

	int count, i;
	int index;

	while ((scn = elf_nextscn(elf, scn)) != NULL) {
		if (gelf_getshdr(scn, &shdr) != &shdr)
			errx(EXIT_FAILURE, "getshdr() failed: %s.", elf_errmsg(-1));

		if ((name = elf_strptr(elf, shstrndx, shdr.sh_name)) == NULL)
			errx(EXIT_FAILURE, "elf_strptr() failed: %s.", elf_errmsg(-1));

		if (strcmp(name, ".rel.plt") == 0) {
			edata = elf_getdata(scn, edata);

			count = shdr.sh_size / shdr.sh_entsize;

			for (i = 0; i < count; i++) {
				gelf_getrel (edata, i, &rel);
				struct call_map *t_map = new struct call_map();
				index = ELF64_R_SYM(rel.r_info); // FIXME: 32? 64?
				t_map->addr = plt_base + index*(0x10);
				//t_map->func_name = "<empty>";
				cout<<"#"<<i<<": sym index = "<<index<<":"<<hex<<t_map->addr<<endl;
				call_table.insert(pair<int, call_map *>(index, t_map));
			}

		}
	}
}

void get_dynsym(Elf *elf, size_t shstrndx, map <int, call_map *> &call_table){

	GElf_Shdr shdr;
	Elf_Scn *scn = NULL;
	GElf_Sym sym;
	char *name;
	static Elf_Data *edata; //It's important that edata is global/static

	int count, i;

	while ((scn = elf_nextscn(elf, scn)) != NULL) {
		gelf_getshdr(scn, &shdr);
		if (shdr.sh_type == SHT_DYNSYM) {
			edata = elf_getdata(scn, edata);

			count = shdr.sh_size / shdr.sh_entsize;

			for (i = 0; i < count; i++) {
				gelf_getsym(edata, i, &sym);

				if(ELF32_ST_TYPE(sym.st_info) == STT_FUNC){
					if ((name = elf_strptr(elf, shdr.sh_link, sym.st_name)) == NULL)
						errx(EXIT_FAILURE, "elf_strptr() failed: %s.", elf_errmsg(-1));
					//printf("%s\n", name);
					call_table.at(i)->func_name = name;
					//struct call_map * t_map = new struct call_map();
					//t_map->addr = call_table[i]->addr;
					//t_map->func_name = (char *)malloc(sizeof(char)*256);
					//call_table.erase(i);
					//strcpy(t_map->func_name, name);
					//call_table.insert(pair<int, call_map *>(i, t_map));
				}else{
					call_table.erase(i);
				}
			}

		}
	}
}

Elf64_Addr get_pltbase(Elf *elf, size_t shstrndx){
	//Get plt base address
	GElf_Shdr shdr;
	Elf_Scn *scn = NULL;
	Elf64_Addr res = 0;

	char *name;
	while ((scn = elf_nextscn(elf, scn)) != NULL) {
		if (gelf_getshdr(scn, &shdr) != &shdr)
			errx(EXIT_FAILURE, "getshdr() failed: %s.", elf_errmsg(-1));

		if ((name = elf_strptr(elf, shstrndx, shdr.sh_name)) == NULL)
			errx(EXIT_FAILURE, "elf_strptr() failed: %s.", elf_errmsg(-1));

		if (strcmp(name, ".plt") == 0) {
			(void) printf("Section %-4.4jd %s %x\n", (uintmax_t) elf_ndxscn(scn), name, shdr.sh_addr);
			res = shdr.sh_addr;
			break;
		}
	}

	return res;
}

void get_call_table(char *filename, map <int, call_map *> &call_table){

	int fd, i;
	Elf *elf;
	size_t shstrndx;

	if (elf_version(EV_CURRENT) == EV_NONE)
		errx(EXIT_FAILURE, "ELF library initialization "
				"failed: %s", elf_errmsg(-1));

	if ((fd = open(filename, O_RDWR, 0)) < 0)
		err(EXIT_FAILURE, "open \%s\" failed", filename);

	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		errx(EXIT_FAILURE, "elf_begin() failed: %s.", elf_errmsg(-1));

	if (elf_kind(elf) != ELF_K_ELF)
		errx(EXIT_FAILURE, "%s is not an ELF object.", filename);

	if (elf_getshdrstrndx(elf, &shstrndx) != 0)
		errx(EXIT_FAILURE, "elf_getshdrstrndx() failed: %s.", elf_errmsg(-1));

	//get plt base address
	plt_base = get_pltbase(elf, shstrndx);

	//set elf back to the beginning
	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		errx(EXIT_FAILURE, "elf_begin() failed: %s.", elf_errmsg(-1));

	get_relplt(elf, shstrndx, call_table);

	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		errx(EXIT_FAILURE, "elf_begin() failed: %s.", elf_errmsg(-1));
	get_dynsym(elf, shstrndx, call_table);

	printf("%d\n",call_table.size());
	map <int, call_map *>::iterator it;
	for(it = call_table.begin(); it != call_table.end(); it ++){
		//printf("%d#%x %s\n",it->first, it->second->addr, it->second->func_name);
		cout<<it->first<<":"<<hex<<it->second->addr<<" "<<it->second->func_name<<endl;
	}


	(void) elf_end(elf);
	(void) close(fd);

}

