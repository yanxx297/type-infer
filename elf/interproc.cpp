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


using namespace std;

struct addr_range plt_range;
struct addr_range text_range;

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
				t_map->addr = plt_range.low_addr + (i+1)*(0x10);
				//t_map->func_name = "<empty>";
				//cout<<"#"<<i<<": sym index = "<<index<<":"<<hex<<t_map->addr<<endl;
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

				if(ELF32_ST_TYPE(sym.st_info) == STT_FUNC && call_table.count(i) > 0){
					if ((name = elf_strptr(elf, shdr.sh_link, sym.st_name)) == NULL)
						errx(EXIT_FAILURE, "elf_strptr() failed: %s.", elf_errmsg(-1));
					//printf("%d -> %s\n", i, name);
					call_table.at(i)->func_name = std::string(name);
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

void get_sec_range(Elf *elf, char *sec_name, size_t shstrndx, Elf64_Addr *low_addr, Elf64_Addr *high_addr){
	//Get plt base address
	GElf_Shdr shdr;
	Elf_Scn *scn = NULL;

	char *name;
	while ((scn = elf_nextscn(elf, scn)) != NULL) {
		if (gelf_getshdr(scn, &shdr) != &shdr)
			errx(EXIT_FAILURE, "getshdr() failed: %s.", elf_errmsg(-1));

		if ((name = elf_strptr(elf, shstrndx, shdr.sh_name)) == NULL)
			errx(EXIT_FAILURE, "elf_strptr() failed: %s.", elf_errmsg(-1));

		if (strcmp(name, sec_name) == 0) {
			//(void) printf("Section %-4.4jd %s %x\n", (uintmax_t) elf_ndxscn(scn), name, shdr.sh_addr);
			*(low_addr) = shdr.sh_addr;
			*(high_addr) = shdr.sh_addr + shdr.sh_size;
			break;
		}
	}
}


void get_call_table(char *filename, map <int, call_map *> &call_table, struct addr_range * text){

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

	//get plt section range
	get_sec_range(elf, ".plt", shstrndx, &(plt_range.low_addr), &(plt_range.high_addr));
	//cout<<hex<<plt_range.low_addr<<" "<<hex<<plt_range.high_addr<<endl;
	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		errx(EXIT_FAILURE, "elf_begin() failed: %s.", elf_errmsg(-1));

	//get text section range
	get_sec_range(elf, ".text", shstrndx, &(text_range.low_addr), &(text_range.high_addr));
	text->high_addr = text_range.high_addr;
	text->low_addr = text_range.low_addr;
	//cout<<hex<<text_range.low_addr<<" "<<hex<<text_range.high_addr<<endl;
	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		errx(EXIT_FAILURE, "elf_begin() failed: %s.", elf_errmsg(-1));

	get_relplt(elf, shstrndx, call_table);
	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		errx(EXIT_FAILURE, "elf_begin() failed: %s.", elf_errmsg(-1));
	get_dynsym(elf, shstrndx, call_table);


	(void) elf_end(elf);
	(void) close(fd);

}

