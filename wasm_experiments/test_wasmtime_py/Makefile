.PHONY: all clean info0, info1

WASI_SDK_PATH = $(HOME)/Downloads/wasi-sdk-12.0

CC = ${WASI_SDK_PATH}/bin/clang --sysroot=${WASI_SDK_PATH}/share/wasi-sysroot -Wl,--export-all

all: foo.wasm

foo.wasm: foo.c
	$(CC) foo.c -o foo.wasm

clean:
	rm -f foo.bc foo.o foo.wasm
