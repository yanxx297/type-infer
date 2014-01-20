CC=g++
CFLAGS=-Wall -w 
I_VINE=-I/home/yanxx297/binary_analysis/dwarf-20130207/libdwarf -I/home/yanxx297/binary_analysis/vine-1.0/libasmir/src/include -I/home/yanxx297/binary_analysis/vine-1.0/VEX/pub -I/home/yanxx297/binary_analysis/vine-1.0/libasmir
INCLUDE=-I/home/yanxx297/project/src/include 
LIBS=-lasmir -lvex -lbfd -liberty -lopcodes -ldwarf -lelf

all: debug_info.o dvar.o type_dwarf_util.o location.o

debug_info.o: debug_info.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c debug_info.cpp

	
dvar.o: dvar.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c dvar.cpp
	
	
type_dwarf_util.o: type_dwarf_util.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c type_dwarf_util.cpp
	
	
location.o: location.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c location.cpp
	