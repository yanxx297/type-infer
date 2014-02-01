include ../Makefile.variable

all: infer.o main.o ptr_handler.o

infer.o: infer.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c infer.cpp -g
	
main.o: main.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c main.cpp -g
	
ptr_handler.o: ptr_handler.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c ptr_handler.cpp -g