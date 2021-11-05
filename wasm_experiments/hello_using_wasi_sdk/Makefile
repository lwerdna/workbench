.PHONY: all clean run

WASI_SDK_PATH = $(HOME)/Downloads/wasi-sdk-12.0

CC = ${WASI_SDK_PATH}/bin/clang --sysroot=${WASI_SDK_PATH}/share/wasi-sysroot -Wl,--export-all

all: helloworld.wasm

helloworld.wasm: helloworld.c
	$(CC) helloworld.c -o helloworld.wasm

run:
	wasmtime ./helloworld.wasm

clean:
	rm -f helloworld.wasm
