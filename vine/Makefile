include ../Makefile.variable

all: tmp_s.o vine_api.o

tmp_s.o: tmp_s.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c tmp_s.cpp -g
	
vine_api.o: vine_api.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c vine_api.cpp -g