all: hello.o hello_big.o

hello: hello.o
	ld -o hello hello.o \
	-lSystem \
	-syslibroot `xcrun -sdk macosx --show-sdk-path` \
	-e _start \
	-arch arm64 

hello.o: hello.s
	as -arch arm64 -o hello.o hello.s

hello_big.o: hello_big.s
	as -arch arm64 -o hello_big.o hello_big.s

gen: gen.py
	./gen.py > hello_big.s

disassemble:
	objdump --disassemble ./hello.o

relocs:
	llvm-readobj -r --expand-relocs ./hello.o

relocations: relocs
