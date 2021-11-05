#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
	return 0;
}

int add(int a, int b)
{
	return a + b;
}

char *animal0()
{
	return "aardvark";
}

uint8_t *create_buf()
{
	return malloc(256);
}

struct addends
{
	uint32_t a;
	uint32_t b;
};

int add_struct(struct addends arg)
{
	return arg.a + arg.b;
}
