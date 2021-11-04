.PHONY: all clean info0, info1

CLANG = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/clang
DIS = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/llvm-dis
LLC = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/llc
LD = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/wasm-ld

all: foo.wasm

foo.wasm: foo.o
	$(LD) --no-entry --export-all foo.o -o foo.wasm

foo.o: foo.bc
	$(LLC) -march=wasm32 -filetype=obj ./foo.bc -o foo.o

foo.bc: foo.c
	$(CLANG) --target=wasm32 -emit-llvm -c foo.c -o foo.bc

info0:
	cat ./foo.bc | $(DIS)

info1:
	wasm-objdump --headers ./foo.o
	wasm-objdump --disassemble ./foo.o
	wasm-objdump --details ./foo.o

clean:
	rm -f foo.bc foo.o foo.wasm
