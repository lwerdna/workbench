// sample.c
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

// You _probably_ don't have these old crt1.o binaries.
uint64_t X asm("dyld_stub_binding_helper") = 0;

uint64_t SERIAL = 0xdeadbeef;

void transmogrify(uint64_t v) {
    srand(time(NULL));
    SERIAL ^= v & rand();
}
