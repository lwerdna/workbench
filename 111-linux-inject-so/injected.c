#include <stdio.h>
#include <stdlib.h>

__attribute__ ((constructor))
static void init(int argc, char **argv)
{
	printf("Hello from injected!\n");
}
