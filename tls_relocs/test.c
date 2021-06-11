#include <stdio.h>

/* from aaa */
int value();
int *address();
int value_static();
int *address_static();
int value_extern();
int *address_extern();

int main(int ac, char **av)
{
	printf("value(): 0x%X\n", value());
	printf("address(): %p\n", address());
	printf("value_static(): 0x%X\n", value_static());
	printf("address_static(): %p\n", address_static());
	printf("value_extern(): 0x%X\n", value_extern());
	printf("address_extern(): %p\n", address_extern());
	return 0;
}
