.PHONY: all clean info0, info1

WASI_SDK_PATH = $(HOME)/Downloads/wasi-sdk-12.0
WASI_SYSROOT = $(WASI_SDK_PATH)/share/wasi-sysroot 

CC = ${WASI_SDK_PATH}/bin/clang
LD = ${WASI_SDK_PATH}/bin/wasm-ld

EXPORTS = --export=add,--export=create_buf,--export=animal0,--export=add_struct

all: foo.wasm

foo.wasm: foo.c
	$(CC) --sysroot=$(WASI_SYSROOT) -Wl,$(EXPORTS) foo.c -o foo.wasm

clean:
	rm -f foo.bc foo.o foo.wasm
