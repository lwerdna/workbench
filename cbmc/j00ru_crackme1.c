// C recreation of http://crackmes.cf/users/j00ru/crackme_1.0_32bit_hash_by_j00ru/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>

void check()
{
	char password[10];
	password[9] = '\0';
	int32_t length;
	//int32_t length = strlen(password);

	int32_t a = 0;
	for (int32_t i = 0; i < length; i = i + 1)
		a = a + password[i];
	printf("a: 0x%08X\n", a);

	int32_t b = 0;
	for (int32_t j = 0; j < length; j = j + 1)
		b = ((b + password[j]) * a) ^ 0x9876;
	printf("b: 0x%08X\n", b);

	int32_t c = 0;
	for (int32_t k = 0; k < length; k = k + 1)
		c = ((c + (password[k] ^ 0xff)) ^ b) + 0xabcd123;
	printf("c: 0x%08X\n", c);

	int32_t d = a * 0x4d2;
	for (int32_t l = 0; l < a; l = l + 1) {
		int32_t eax_23 = ((l + c) ^ a) ^ 0x4d200;
		d = (((l + 0x1234ab) ^ (d + l)) ^ 0x50f00aa2) + ((eax_23 * eax_23) - 0xaaf);
		for (int32_t m = 0; m < length; m = m + 1) {
			int32_t var_12c_5 = (((d * length) - length) ^ m) - b;
			d = (var_12c_5 * var_12c_5) ^ b;
		}		
	}
	printf("d: 0x%08X\n", d);

	assert(d != 0xcd65ab89);
	/*
	if (d != 0xcd65ab89)
		printf("Shit... Bad password...\n");
	else
		printf("YEAH! GOOD WORK!!!\n");
	*/
};

int main(int ac, char **av)
{
};
