__thread int var0 = 0x29a;
int value(void) { return var0; }
int *address(void) { return &var0;	}

static __thread int var1 = 0x29b;
int value_static() { return var1; }
int *address_static() { return &var1; }

extern __thread int var2;
int value_extern() { return var2; }
int *address_extern() { return &var2; }
