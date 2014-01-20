CC=g++
LDFLAGS=-L/home/yanxx297/binary_analysis/dwarf-20130207/libdwarf -L/home/yanxx297/binary_analysis/vine-1.0/libasmir/src -L/home/yanxx297/binary_analysis/vine-1.0/VEX
CFLAGS=-Wall -w 
I_VINE=-I/home/yanxx297/binary_analysis/dwarf-20130207/libdwarf -I/home/yanxx297/binary_analysis/vine-1.0/libasmir/src/include -I/home/yanxx297/binary_analysis/vine-1.0/VEX/pub -I/home/yanxx297/binary_analysis/vine-1.0/libasmir
#INCLUDE=-I/home/yanxx297/project/src/include 
LIBS=-lasmir -lvex -lbfd -liberty -lopcodes -ldwarf -lelf
MAKE=make

all: infer

#infer: main.o infer.o ptr_handler.o debug_info.o type_dwarf_util.o dvar.o location.o vertex.o vine_api.o tmp_s.o debug_tool.o draw_dot.o
infer: task_dwarf task_vine task_graph task_util task_infer
	$(CC) $(CFLAGS) $(I_VINE) main.o infer.o ptr_handler.o debug_tool.o draw_dot.o debug_info.o type_dwarf_util.o dvar.o location.o vertex.o vine_api.o tmp_s.o $(LDFLAGS) $(LIBS) -o infer
	rm *.o

task_dwarf:
	cd dwarf && $(MAKE) && cp *.o ../
	
task_vine:
	cd vine && $(MAKE) && cp *.o ../
	
task_graph:
	cd graph && $(MAKE) && cp *.o ../
	
task_util:
	cd util && $(MAKE) && cp *.o ../
	
task_infer:
	cd type_infer && $(MAKE) && cp *.o ../

clean:
	rm infer
	find . -name \*.o -type f -delete