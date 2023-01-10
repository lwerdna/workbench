# assemble/compile ELF64 from macos, requires nasm and llvm

LD_LLD = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/ld.lld

all: example

example: example.o
	$(LD_LLD) example.o -o example

example.o: example.s
	nasm example.s -f elf64 -o example.o

clean:
	rm -f example example.o
