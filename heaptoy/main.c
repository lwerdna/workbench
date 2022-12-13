#include <stdio.h>

#include "malloc.h"

int main(int ac, char **av)
{
	printf("main() here\n");
	
	char *buf = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf);

	buf = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf);

	buf = dlmalloc(1024);
	printf("allocated buffer: %p\n", buf);
}
