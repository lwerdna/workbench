// C recreation of http://crackmes.cf/users/j00ru/crackme_1.0_32bit_hash_by_j00ru/
//
// this won't solve the crackme
// crackme enforces hash(???) == 0xcd65ab89
//             test hash("aardvark") == 0xF55356C3
// cbmc cannot find "aardvark" even with knowledge that hash input is 8 chars

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>

uint32_t hash(char *password, int len)
{
	int32_t a = 0;
	for (int32_t i = 0; i < len; i = i + 1)
		a = a + password[i];
	//printf("a: 0x%08X\n", a);

	int32_t b = 0;
	for (int32_t j = 0; j < len; j = j + 1)
		b = ((b + password[j]) * a) ^ 0x9876;
	//printf("b: 0x%08X\n", b);

	int32_t c = 0;
	for (int32_t k = 0; k < len; k = k + 1)
		c = ((c + (password[k] ^ 0xff)) ^ b) + 0xabcd123;
	//printf("c: 0x%08X\n", c);

	uint32_t d = a * 0x4d2;
	for (int32_t l = 0; l < a; l = l + 1) {
		int32_t eax_23 = ((l + c) ^ a) ^ 0x4d200;
		d = (((l + 0x1234ab) ^ (d + l)) ^ 0x50f00aa2) + ((eax_23 * eax_23) - 0xaaf);
		for (int32_t m = 0; m < len; m = m + 1) {
			int32_t var_12c_5 = (((d * len) - len) ^ m) - b;
			d = (var_12c_5 * var_12c_5) ^ b;
		}		
	}
	//printf("d: 0x%08X\n", d);

	return d;
	/*
	if (d != 0xcd65ab89)
		printf("Shit... Bad password...\n");
	else
		printf("YEAH! GOOD WORK!!!\n");
	*/
};
	
#define PWLEN 8
uint32_t hash_unrolled()
{
	char password[PWLEN+1];
	password[PWLEN] = '\0';

	//strcpy(password, "aardvark");

	int32_t a = 0;
	#if PWLEN>0
	a += password[0];
	#endif
	#if PWLEN>1
	a += password[1];
	#endif
	#if PWLEN>2
	a += password[2];
	#endif
	#if PWLEN>3
	a += password[3];
	#endif
	#if PWLEN>4
	a += password[4];
	#endif
	#if PWLEN>5
	a += password[5];
	#endif
	#if PWLEN>6
	a += password[6];
	#endif
	#if PWLEN>7
	a += password[7];
	#endif

	int32_t b = 0;
	#if PWLEN>0
	b = ((b + password[0])*a)^0x9876;
	#endif
	#if PWLEN>1
	b = ((b + password[1])*a)^0x9876;
	#endif
	#if PWLEN>2
	b = ((b + password[2])*a)^0x9876;
	#endif
	#if PWLEN>3
	b = ((b + password[3])*a)^0x9876;
	#endif
	#if PWLEN>4
	b = ((b + password[4])*a)^0x9876;
	#endif
	#if PWLEN>5
	b = ((b + password[5])*a)^0x9876;
	#endif
	#if PWLEN>6
	b = ((b + password[6])*a)^0x9876;
	#endif
	#if PWLEN>7
	b = ((b + password[7])*a)^0x9876;
	#endif

	int32_t c = 0;
	#if PWLEN>0
	c = ((c + (password[0] ^ 0xff)) ^ b) + 0xabcd123;
	#endif
	#if PWLEN>1
	c = ((c + (password[1] ^ 0xff)) ^ b) + 0xabcd123;
	#endif
	#if PWLEN>2
	c = ((c + (password[2] ^ 0xff)) ^ b) + 0xabcd123;
	#endif
	#if PWLEN>3
	c = ((c + (password[3] ^ 0xff)) ^ b) + 0xabcd123;
	#endif
	#if PWLEN>4
	c = ((c + (password[4] ^ 0xff)) ^ b) + 0xabcd123;
	#endif
	#if PWLEN>5
	c = ((c + (password[5] ^ 0xff)) ^ b) + 0xabcd123;
	#endif
	#if PWLEN>6
	c = ((c + (password[6] ^ 0xff)) ^ b) + 0xabcd123;
	#endif
	#if PWLEN>7
	c = ((c + (password[7] ^ 0xff)) ^ b) + 0xabcd123;
	#endif

	uint32_t d = a * 0x4d2;
	for (int32_t l = 0; l < a; l = l + 1) {
		int32_t eax_23 = ((l + c) ^ a) ^ 0x4d200;
		d = (((l + 0x1234ab) ^ (d + l)) ^ 0x50f00aa2) + ((eax_23 * eax_23) - 0xaaf);
		for (int32_t m = 0; m < PWLEN; m = m + 1) {
			int32_t var_12c_5 = (((d * PWLEN) - PWLEN) ^ m) - b;
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
	// test goal: can CBMC find "aardvark"?
	assert(hash_unrolled() == 0xF55356C3);

	// crackme goal
	// assert(hash_unrolled() == 0xcd65ab89);
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

	hash_unrolled();

	printf("PASS\n");

	return 0;
};
