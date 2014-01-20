CC=g++
CFLAGS=-Wall -w 
I_VINE=-I/home/yanxx297/binary_analysis/dwarf-20130207/libdwarf -I/home/yanxx297/binary_analysis/vine-1.0/libasmir/src/include -I/home/yanxx297/binary_analysis/vine-1.0/VEX/pub -I/home/yanxx297/binary_analysis/vine-1.0/libasmir
INCLUDE=-I/home/yanxx297/project/src/include 
LIBS=-lasmir -lvex -lbfd -liberty -lopcodes -ldwarf -lelf

all: debug_tool.o draw_dot.o

debug_tool.o: debug_tool.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c debug_tool.cpp
	
draw_dot.o: draw_dot.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c draw_dot.cpp
	