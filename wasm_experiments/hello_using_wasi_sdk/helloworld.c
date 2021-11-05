// build:
// $ /path/to/wasi-sdk-12.0/bin/clang --sysroot=/path/to/wasi-sdk-12.0/share/wasi-sysroot helloworld.c -o helloworld.wasm
// run:
// $ wasmtime ./helloworld.wasm

#include <stdio.h>

int main(int argc, char **argv)
{
	printf("Hello, world!\n");

	return 0;
}

int add(int a, int b)
{
	return a + b;
}
