include ../Makefile.variable

all: infer.o main.o ptr_handler.o

infer.o: infer.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c infer.cpp $(FLAGS)
	
main.o: main.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c main.cpp $(FLAGS)
	
ptr_handler.o: ptr_handler.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c ptr_handler.cpp $(FLAGS)