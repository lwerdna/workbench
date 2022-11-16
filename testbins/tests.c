/* tests
 * gcc tests.c -o tests
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

void mark_success(void)
{
	return;
}

void mark_failure(void)
{
	return;
}

int add(int a, int b)
{
	return a+b;
}

void print_2path(int a)
{
	if(a<10) {
		mark_success();
		printf("less\n");
	}
	else {
		mark_failure();
		printf("more\n");
	}
}

int multiexit(unsigned int a)
{
	if(a<10) {
		return 1;
	}
	else if(a<20) {
		return 2;
	}
	else if(a<30) {
		return 3;
	}
	else if(a<100) {
		return 4;
	}
	return 0;
}

///* Write a program that prints the numbers from 1 to 100. But for multiples of three print “Fizz” instead of the number and for the multiples of five print “Buzz”. For numbers which are multiples of both three and five print “FizzBuzz”.*/
//void fizzbuzz(void)
//{
//	for(int i=1; i<=100; ++i) {
//		if(i%15 == 0) printf("FizzBuzz\n");
//		else if(i%3 == 0) printf("Fizz\n");
//		else if(i%5 == 0) printf("Buzz\n");
//		else printf("%d\n", i);
//	}
//}
//
//int collatz_message(char *message, int n)
//{
//	if(n % 2) {
//		/* is odd */
//		n = 3*n + 1;
//	}
//	else {
//		/* is even */
//		n = n / 2;
//	}
//
//	if(message)
//		printf("%s: %d", message, n);
//
//	return n;
//}
//

void one_loop(void)
{
	int i;

	printf("hi\n");

	for(i=0; i<10; ++i)
		printf("there\n");

	printf("bro");
}

void some_loops(void)
{
	int i=0, j=0, k=0;

	while(i<10) {
		printf("i: %d\n", i++);
	}

	printf("even numbers:\n");
	for(i=0; i<16; i+=2)
		printf("%d ", i);

	printf("\nnot a loop: %d\n", i);

	printf("\nnumbers with b1 set:\n");
	for(i=0; i<16; i++)
		if(i & 2)
			printf("%d ", i);

	printf("\nnot a loop: %d\n", i);

	printf("\nnested loops:\n");
	for(i=0; i<16; i++)
		for(j=0; j<17; j++)
			for(k=0; k<18; k++)
				printf("%d %d %d\n", i, j, k);

	printf("\nnot a loop: %d\n", i);

	while(1)
		printf("single node forever loop!\n");

	printf("\nnot a loop: %d\n", i);
}

/*
 a b c
 d e f
 g h i
 */
int magic_square(int a, int b, int c, int d, int e, int f, int g, int h, int i)
{
	/* valid ranges */
	if(a < 0 || a > 9) return -1;
	if(b < 0 || b > 9) return -1;
	if(c < 0 || c > 9) return -1;
	if(d < 0 || d > 9) return -1;
	if(e < 0 || e > 9) return -1;
	if(f < 0 || f > 9) return -1;
	if(g < 0 || g > 9) return -1;
	if(h < 0 || h > 9) return -1;
	if(i < 0 || i > 9) return -1;

	/* they must be unique */
	if(a == b || a == c || a == d || a == e || a == f || a == g || a == h || a == i) return -1;
	if(b == c || b == d || b == e || b == f || b == g || b == h || b == i) return -1;
	if(c == d || c == e || c == f || c == g || c == h || c == i) return -1;
	if(d == e || d == f || d == g || d == h || d == i) return -1;
	if(e == f || e == g || e == h || e == i) return -1;
	if(f == g || f == h || f == i) return -1;
	if(g == h || g == i) return -1;
	if(h == i) return -1;

	/* rows */
	if(a+b+c != 15) return -1;
	if(d+e+f != 15) return -1;
	if(g+h+i != 15) return -1;

	/* columns */
	if(a+d+g != 15) return -1;
	if(b+e+h != 15) return -1;
	if(c+f+i != 15) return -1;

	/* diagonals */
	if(a+e+i != 15) return -1;
	if(c+e+g != 15) return -1;

	/* success */
	return 0;
}

/*
 * arg1 in rdi
 * arg2 in rsi
 * arg3 in rdx
 * arg4 in rcx
 * arg5 in r8
 * arg6 in r9
 * arg7 in [rsp+0x8] or [rbp+0x10]
 * arg8 in [rsp+0x10] or [rbp+0x18]
 * arg9 in [rsp+0x18] or [rbp+0x20]
 * ...
 */
int stack_args(int arg1, int arg2, int arg3, int arg4, int arg5, int arg6, int arg7, int arg8, int arg9)
{
	(void)arg1; // rdi
	(void)arg2; // rsi
	(void)arg3; // rdx
	(void)arg4; // rcx
	(void)arg5; // r8
	(void)arg6; // r9

	// arg7, arg8, arg9 on stack

	if(arg7 == 7) {
		if(arg8 == 8) {
			if(arg9 == 9) {
				printf("PASS!\n");
				return 0;
			}
			else {
				printf("arg9 FAIL!\n");
				return -1;
			}
		}
		else {
			printf("arg8 FAIL!\n");
			return -1;
		}
	}
	else {
		printf("arg7 FAIL!\n");
		return -1;
	}
}

int reg_args(int arg1, int arg2, int arg3)
{
	if(arg1 == 7) {
		if(arg2 == 8) {
			if(arg3 == 9) {
				printf("PASS!\n");
				return 0;
			}
			else {
				printf("arg3 FAIL!\n");
				return -1;
			}
		}
		else {
			printf("arg2 FAIL!\n");
			return -1;
		}
	}
	else {
		printf("arg1 FAIL!\n");
		return -1;
	}
}

int xtea_1cycle(uint32_t k0, uint32_t k1, uint32_t k2, uint32_t k3)
{
	uint32_t a0 = 0x00112233;
	uint32_t b0 = 0x44556677;
	uint32_t a1 = a0 + ((((b0 << 4) ^ (b0 >> 5)) + b0) ^ (0x00000000 + k0));
	uint32_t b1 = b0 + ((((a1 << 4) ^ (a1 >> 5)) + a1) ^ (0x9E3779B9 + k3));
	uint32_t a2 = a1 + ((((b1 << 4) ^ (b1 >> 5)) + b1) ^ (0x9E3779B9 + k1));
	uint32_t b2 = b1 + ((((a2 << 4) ^ (a2 >> 5)) + a2) ^ (0x3C6EF372 + k2));
	if(a2 == 0x5A055406 && b2 == 0xEC8F42BD)
	{
		printf("PASS\n");
		return 0;
	}
	else
	{
		printf("FAIL\n");
		return -1;
	}
}

/* in two-round XTEA, we know:
 * 00112233-44556677 -> 5A055406-EC8F42BD
 * AAAAAAAA-BBBBBBBB -> 9BE82231-A67A3F1D
 *
 * for only 9 possible keys:
 * 00010203-04050607-08090A0B-0C0D0E0F
 * 00012322-C205D065-4808FA32-CC0F1E64
 * 00010322-C205F065-4808FA32-CC0D3F64
 * 00612322-1A45D065-CC08FA32-5A301E64
 * 81C0D722-9ADAFF5E-ED917733-DBCC2A01
 * 01C0D722-1ADAFF5E-ED917733-5FCC2A01
 * ED00FA2B-7CDF3153-AB8F4B73-BB698840
 * 85707722-16D6635E-6E61F733-0C1C8F01
 * 05707722-96D6635E-6E61F733-881C8F01
 *
 */
int xtea_2cycle(uint32_t k0, uint32_t k1, uint32_t k2, uint32_t k3)
{
	uint32_t a0 = 0x00112233;
	uint32_t b0 = 0x44556677;
	uint32_t a1 = a0 + ((((b0 << 4) ^ (b0 >> 5)) + b0) ^ (0x00000000 + k0));
	uint32_t b1 = b0 + ((((a1 << 4) ^ (a1 >> 5)) + a1) ^ (0x9E3779B9 + k3));
	uint32_t a2 = a1 + ((((b1 << 4) ^ (b1 >> 5)) + b1) ^ (0x9E3779B9 + k1));
	uint32_t b2 = b1 + ((((a2 << 4) ^ (a2 >> 5)) + a2) ^ (0x3C6EF372 + k2));
	/* this allows for many many many keys */
	if(a2 == 0x5A055406 && b2 == 0xEC8F42BD)
	{
		uint32_t a0 = 0xAAAAAAAA;
		uint32_t b0 = 0xBBBBBBBB;
		uint32_t a1 = a0 + ((((b0 << 4) ^ (b0 >> 5)) + b0) ^ (0x00000000 + k0));
		uint32_t b1 = b0 + ((((a1 << 4) ^ (a1 >> 5)) + a1) ^ (0x9E3779B9 + k3));
		uint32_t a2 = a1 + ((((b1 << 4) ^ (b1 >> 5)) + b1) ^ (0x9E3779B9 + k1));
		uint32_t b2 = b1 + ((((a2 << 4) ^ (a2 >> 5)) + a2) ^ (0x3C6EF372 + k2));

		/* this restricts possible keys to to 9 */
		if(a2 == 0x9BE82231 && b2 == 0xA67A3F1D)
		{
			printf("PASS\n");
			return 0;
		}
		else
		{
			printf("FAIL\n");
			return -1;
		}
	}
	else
	{
		printf("FAIL\n");
		return -1;
	}
}

int quadrants(int x, int y)
{
	if(x < 5 && y < 5)
	{
		printf("QUADRANT 2\n");
		return 0;
	}
	else if(x < 5 && y < 10)
	{
		printf("QUADRANT 1\n");
		return 0;
	}
	else if(x < 10 && y < 5)
	{
		printf("QUADRANT 3\n");
		return 0;
	}
	else if(x < 10 && y < 10)
	{
		printf("QUADRANT 4\n");
		return 0;
	}
	else
	{
		printf("QUADRANT NONE\n");
		return -1;
	}
}

int loop0()
{
	int sum = 0, i;

	for(i=0; i<8; ++i)
	{
		sum = sum + i;
	}

	// 0+1+2+...+7 = 28
	if(sum > 20)
	{
		printf("YES\n");
		return 0;
	}
	else
	{
		printf("NO\n");
		return -1;
	}
}

int loop1()
{
	int sum = 0;

	if(sum > 20)
	{
		printf("YES\n");
		return 0;
	}
	else
	{
		printf("NO\n");
		return -1;
	}
}

void switcher(unsigned int a, unsigned int b)
{
	switch(a * 5 + b)
	{
		case 2:
		case 3:
		case 5:
		case 7: printf("PRIME, <10\n"); break;

		case 11:
		case 13:
		case 17:
		case 19: printf("PRIME, <20\n"); break;

		case 23:
		case 27:
		case 29: printf("PRIME, <30\n"); break;

		default:
			printf("COMPOSITE OR OUT OF RANGE\n");
	}
}

/* this attempt to compile to the running example from the DREAM "no more gotos" decompiler PDF */

/*
void dream_cfg(bool cond_A, bool cond_b1, bool cond_b2, bool cond_c1, bool cond_c2, bool cond_d1, bool cond_d2, bool cond_d3)
{
	goto A;

	A:
	if(cond_A)
		goto c1;
	else
		goto b1;

	//
	// R1
	//
	c1:
	if(cond_c1)
		goto n1;
	else
		goto c2;

	n1:
	goto c1;

	c2:
	if(cond_c2)
		goto n2;
	else
		goto n3;

	n2:
	goto n9;

	n3:
	goto c3;

	c3:
	goto c1;

	//
	// R2
	//
	b1:
	if(cond_b1)
		goto b2;
	else
		goto n4;
	
	b2:
	if(cond_b2)
		goto n6;
	else
		goto n5;

	n4:
	goto n5;

	n5:
	goto n7;

	n6:
	goto n7;

	n7:
	goto d1;

	//
	// R3
	//
	d1:
	if(cond_d1)
		goto d3;
	else
		goto d2;

	d2:
	if(cond_d2)
		goto n8;
	else
		goto n9;

	d3:
	if(cond_d3)
		goto n8;
	else
		goto n9;

	n8:
	goto d1;

	n9:
	return;
}
*/

int main(int ac, char **av)
{
//	fizzbuzz();
	print_2path(5);
	print_2path(15);
	printf("hi\n");
	printf("quadrants(3,3)=%d\n", quadrants(3,3));
	printf("quadrants(3,7)=%d\n", quadrants(3,7));
	printf("quadrants(7,3)=%d\n", quadrants(7,3));
	printf("quadrants(7,7)=%d\n", quadrants(7,7));
	printf("quadrants(17,17)=%d\n", quadrants(17,17));
	printf("xtea_1cycle(0x00010203, 0x04050607, 0x08090A0B, 0x0C0D0E0F)=%d\n",
		xtea_1cycle(0x00010203, 0x04050607, 0x08090A0B, 0x0C0D0E0F));
	printf("xtea_2cycle(0x00010203, 0x04050607, 0x08090A0B, 0x0C0D0E0F)=%d\n",
		xtea_2cycle(0x00010203, 0x04050607, 0x08090A0B, 0x0C0D0E0F));
	printf("magic_square(2,7,6,9,5,1,4,3,8)=%d\n", magic_square(2,7,6,9,5,1,4,3,8));
	printf("magic_square(2,2,6,9,5,1,4,3,8)=%d\n", magic_square(2,2,6,9,5,1,4,3,8));
	printf("magic_square(1,2,3,4,5,6,7,8,9)=%d\n", magic_square(1,2,3,4,5,6,7,8,9));
	return 0;
}
