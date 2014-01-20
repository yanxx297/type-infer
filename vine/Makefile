CC=g++
CFLAGS=-Wall -w 
I_VINE=-I/home/yanxx297/binary_analysis/dwarf-20130207/libdwarf -I/home/yanxx297/binary_analysis/vine-1.0/libasmir/src/include -I/home/yanxx297/binary_analysis/vine-1.0/VEX/pub -I/home/yanxx297/binary_analysis/vine-1.0/libasmir
INCLUDE=-I/home/yanxx297/project/src/include 
LIBS=-lasmir -lvex -lbfd -liberty -lopcodes -ldwarf -lelf

all: tmp_s.o vine_api.o

tmp_s.o: tmp_s.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c tmp_s.cpp
	
vine_api.o: vine_api.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c vine_api.cpp