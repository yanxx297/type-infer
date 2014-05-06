include ../Makefile.variable

all: debug_info.o dvar.o type_dwarf_util.o location.o

debug_info.o: debug_info.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c debug_info.cpp $(FLAGS)

	
dvar.o: dvar.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c dvar.cpp $(FLAGS)
	
	
type_dwarf_util.o: type_dwarf_util.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c type_dwarf_util.cpp $(FLAGS)
	
	
location.o: location.cpp
	$(CC) $(CFLAGS) $(INCLUDE) $(I_VINE) -c location.cpp $(FLAGS)
	