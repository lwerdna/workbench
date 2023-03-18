.PHONY: all clean

CLANG = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/clang
LD_LLD = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/ld.lld

puzzle: msquare.o main.o
	$(LD_LLD) msquare.o main.o -o puzzle

main.o: main.s
	nasm main.s -f elf64 -o main.o

msquare.o: msquare.c
	$(CLANG) -g -target x86_64-none-linux-elf -c msquare.c -o msquare.o

clean:
	rm -rf mcore_* *.o puzzle
