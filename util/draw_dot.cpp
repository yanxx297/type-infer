#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>
#include <fcntl.h>
#include <unistd.h>
#include <utility>
#include <stdbool.h>

/*include Vine*/
#include "asm_program.h"
#include "disasm-pp.h"
extern "C"
{
#include "libvex.h"
}
#include "irtoir.h"

/*include libdwarf*/
#include "dwarf.h"
#include "libdwarf.h"

#include "type_common.h"
#include "location.h"
#include "dvar.h"
#include "tmp_s.h"
#include "vine_api.h"
#include "draw_dot.h"

map<int, int> ssa_blist;

void draw_edges(FILE *fp, struct basic_block ** nodelist, int length){
	int i, j;
	for(i = 0; i<length;i++){
		switch(nodelist[i]->branch_type){
		case BIN:{
			fprintf(fp, "%s -> %s;\n", print_nodename(nodelist,i).c_str(),
					print_nodename(nodelist, nodelist[i]->child_jmp).c_str());
			fprintf(fp, "%s -> %s;\n", print_nodename(nodelist,i).c_str(),
					print_nodename(nodelist, nodelist[i]->child_next).c_str());
			break;
		}
		case UN:{
			fprintf(fp, "%s -> %s;\n", print_nodename(nodelist,i).c_str(),
					print_nodename(nodelist, nodelist[i]->child_next).c_str());
			break;
		}
		case UNKNOW:{
			break;
		}
		default:
			break;
		}
	}
}

void draw_box(FILE *fp, struct basic_block ** nodelist, int index){
	int i;
	fprintf(fp, "  %s [label=\"%s\t\\n\\n",print_nodename(nodelist,index).c_str(),print_nodename(nodelist,index).c_str());
	for (i = 0; i < nodelist[index]->blen ; i++){
		if(nodelist[index]->block[i]->stmt_type!=VARDECL && nodelist[index]->block[i]->stmt_type!=COMMENT){
			fprintf(fp, "%s\t\\n",nodelist[index]->block[i]->tostring().c_str());
		}
	}
	fprintf(fp, "\", shape=box];\n");
}

void draw_graph(fblock_ptr func_block, int length){
	FILE *fp;
	int i;

	if((fp = fopen(func_block->func->name.c_str(), "w")) == NULL){
		print_error("Fail to creat file/folder");
		exit(1);
	}
	fprintf(fp, "digraph G {\n");
	//printf("%d\n",length);
	for (i = 0; i < length ; i++){
		draw_box(fp, func_block->block_list, i);
	}
	draw_edges(fp, func_block->block_list, length);
	fprintf(fp, "}\n");
	fclose(fp);
}

