CC=g++
CFLAGS=-Wall -w 
I_VINE=-I/home/yanxx297/binary_analysis/dwarf-20130207/libdwarf -I/home/yanxx297/binary_analysis/vine-1.0/libasmir/src/include -I/home/yanxx297/binary_analysis/vine-1.0/VEX/pub -I/home/yanxx297/binary_analysis/vine-1.0/libasmir
INCLUDE=-I/home/yanxx297/project/src/include
LIBS=-lasmir -lvex -lbfd -liberty -lopcodes -ldwarf -lelf

all: infer.o main.o ptr_handler.o

infer.o: infer.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c infer.cpp
	
main.o: main.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c main.cpp
	
ptr_handler.o: ptr_handler.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c ptr_handler.cpp