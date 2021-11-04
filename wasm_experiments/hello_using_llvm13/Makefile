.PHONY: all clean info0, info1

CLANG = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/clang
DIS = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/llvm-dis
LLC = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/llc
LD = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/wasm-ld

WASI_SYSROOT = $(HOME)/Downloads/wasi-libc/sysroot
WASI_LIBROOT = $(WASI_SYSROOT)/lib/wasm32-wasi

all: helloworld.wasm

helloworld.wasm: helloworld.o
	$(LD) --export-all -L $(WASI_LIBROOT) -lc $(WASI_LIBROOT)/crt1.o helloworld.o -o helloworld.wasm

helloworld.o: helloworld.bc
	$(LLC) -march=wasm32 -filetype=obj ./helloworld.bc -o helloworld.o

helloworld.bc: helloworld.c
	$(CLANG) --target=wasm32 -emit-llvm -c --sysroot=$(WASI_SYSROOT) helloworld.c -o helloworld.bc

info0:
	cat ./helloworld.bc | $(DIS)

info1:
	wasm-objdump --headers ./helloworld.o
	wasm-objdump --disassemble ./helloworld.o
	wasm-objdump --details ./helloworld.o

clean:
	rm -f helloworld.bc helloworld.o helloworld.wasm
