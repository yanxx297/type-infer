# Type Inference
The source code of a type inference research project.
For details of this project, read our [technical report](https://www.cs.umn.edu/research/technical_reports/view/14-006)

#### Build
Run make in ``type-infer-src/``
The following libraries should be installed before this code can be compiled:

- Libdwarf: http://www.prevanders.net/dwarf.html#releases
- Vine: http://bitblaze.cs.berkeley.edu/release/vine-1.0/vine-1.0.tar.gz
	- VEX and STP is required by Vine and included in this repository
	- OCaml is required to compile
- Boost Graph Library: http://www.boost.org/libs/graph/
	- make sure the paths of libraries and the home path are correctly set (you can set them in [type-infer/Makefile.variable](Makefile.variable).)

#### Before Running
For standard libc support, the debug information file of libc must be copy into the same folder of the executable, with ``libc-2.15.so`` as its name. 
This file can be find in ``/usr/lib/debug/lib/i386-linux-gnu`` for Ubuntu Linux distribution.

Before executing the type inference executable ``infer``, make sure struct.log is in the same folder.

#### Usage

	./infer FILENAME [OPTIONS]
	
	-ssaf
		Print out the single-step assignment format Vine IR. 
		Graph is printed out only when this option is turned on.
		
	-single FUNCTION_NUMBER
		Analyze a single function, rather than the entire binary.
		The number of each function is available in the printed out results.
		
	-libc
		Print out variables whose type is defined in standard C library.
		Those variables are ignored by default.
		