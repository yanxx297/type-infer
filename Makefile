include Makefile.variable
MAKE=make

all: infer

#infer: main.o infer.o ptr_handler.o debug_info.o type_dwarf_util.o dvar.o location.o vertex.o vine_api.o tmp_s.o debug_tool.o draw_dot.o
infer: task_dwarf task_vine task_graph task_util task_infer task_elf
	$(LD) $(CFLAGS) $(I_VINE) main.o infer.o ptr_handler.o debug_tool.o draw_dot.o debug_info.o type_dwarf_util.o dvar.o location.o vertex.o vine_api.o tmp_s.o interproc.o $(LDFLAGS) $(LIBS) $(FLAGS) -o infer
	rm *.o

task_dwarf:
	cd dwarf && $(MAKE) && cp *.o ../
	
task_vine:
	cd vine && $(MAKE) && cp *.o ../
	
task_graph:
	cd graph && $(MAKE) && cp *.o ../
	
task_elf:
	cd elf && $(MAKE) && cp *.o ../
	
task_util:
	cd util && $(MAKE) && cp *.o ../
	
task_infer:
	cd type_infer && $(MAKE) && cp *.o ../

clean:
	find . -name \*.o -type f -delete
	rm infer
	