#include <stdio.h>
#include <stdbool.h>

extern int get_signed_int();
extern unsigned int get_unsigned_int();

int main(int ac, char **av)
{
	unsigned a0 = get_unsigned_int();
	unsigned b0 = get_unsigned_int();
	int a1 = get_signed_int();
	int b1 = get_signed_int();

	bool r00 = a0 < b0; // unsigned vs. unsigned
	bool r01 = a0 < b1; // unsigned vs. signed
	bool r10 = a1 < b0; // signed vs. unsigned
	bool r11 = a1 < b1; // signed vs. signed

	bool hmm0 = a0 < 100; // unsigned vs. literal
	bool hmm1 = a1 < 100; // signed vs. literal

	return 0;
}
