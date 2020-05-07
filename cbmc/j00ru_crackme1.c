// C recreation of http://crackmes.cf/users/j00ru/crackme_1.0_32bit_hash_by_j00ru/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>

uint32_t hash(char *password, int len)
{
	int32_t a = 0;
	for (int32_t i = 0; i < len; i = i + 1)
		a = a + password[i];
	printf("a: 0x%08X\n", a);

	int32_t b = 0;
	for (int32_t j = 0; j < len; j = j + 1)
		b = ((b + password[j]) * a) ^ 0x9876;
	printf("b: 0x%08X\n", b);

	int32_t c = 0;
	for (int32_t k = 0; k < len; k = k + 1)
		c = ((c + (password[k] ^ 0xff)) ^ b) + 0xabcd123;
	printf("c: 0x%08X\n", c);

	uint32_t d = a * 0x4d2;
	for (int32_t l = 0; l < a; l = l + 1) {
		int32_t eax_23 = ((l + c) ^ a) ^ 0x4d200;
		d = (((l + 0x1234ab) ^ (d + l)) ^ 0x50f00aa2) + ((eax_23 * eax_23) - 0xaaf);
		for (int32_t m = 0; m < len; m = m + 1) {
			int32_t var_12c_5 = (((d * len) - len) ^ m) - b;
			d = (var_12c_5 * var_12c_5) ^ b;
		}		
	}
	printf("d: 0x%08X\n", d);

	return d;
	/*
	if (d != 0xcd65ab89)
		printf("Shit... Bad password...\n");
	else
		printf("YEAH! GOOD WORK!!!\n");
	*/
};

void check()
{
	#define PWLEN 2
	char password[PWLEN+1];
	password[PWLEN] = '\0';

	assert(hash(password, PWLEN) == 0xcd65ab89);
}

int main(int ac, char **av)
{
	// these are tested against actual crackme values
	// bp 004015a9 in crackme to see computed value comparison
	assert(hash("aardvark", 8) == 0xF55356c3);
	assert(hash("heyhey", 6) == 0x34d8b123);
	assert(hash("salamander", 10) == 0x2121329f);

	if(ac>1)
		printf("hash(\"%s\") == 0x%X\n", av[1], hash(av[1], strlen(av[1])));

	printf("PASS\n");

	return 0;
};
