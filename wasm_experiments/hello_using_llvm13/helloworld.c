#define __wasi__
#include <stdio.h>

int main(int argc, char **argv)
{
	printf("Hello, world!");

	return 0;
}

int add(int a, int b)
{
	return a + b;
}
