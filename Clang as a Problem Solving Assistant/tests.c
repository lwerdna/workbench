/* Test clang/llvm's insight into problems

Functions are written so logic paths which would defy a claim or theorem call print_impossible().
Then, presence of print_impossible(), post optimization, indicates clang/llvm failed to acquire insight.

*/

#ifdef INCLUDE_STDIO
#include <stdio.h>
#else
/* forward declare printf */
int printf(const char *, ...);
#endif

__attribute__((noinline))
void print_impossible()
{
	printf("IMPOSSIBLE\n");
}

__attribute__((noinline))
void print_hello()
{
	printf("HELLO!\n");
}

// THEOREM: n & 0x7 <= 10
void simple_inequality0(int a)
{
	a &= 0b111;
	/* now (int)a <= 7 */

	if(a > 10)
		print_impossible();
	else
		print_hello();
}

// THEOREM: n>20 -> n>10
void simple_inequality1(int n)
{
	if(n <= 20)
		return;
	/* now n > 20 */

	if(n <= 10)
		print_impossible();
	else
		print_hello();
}

#define DIVISIBLE_BY(a,b) ((a) % (b) == 0)

// THEOREM: 4|n -> 2|n
void simple_divisibility0(unsigned int a)
{
	if(!DIVISIBLE_BY(a, 4))
	   	return;
	/* now 4|a */

   	if(DIVISIBLE_BY(a, 2))
		print_hello(); // must execute
   	else
		print_impossible(); // should never execute
}

void simple_divisibility1(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(DIVISIBLE_BY(a, 2))
			print_hello(); // must execute
	   	else
			print_impossible(); // should never execute
	}
}

void simple_divisibility2(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(DIVISIBLE_BY(a, 2))
			while(0); // must execute
	   	else
			print_impossible(); // should never execute
	}
}

void simple_divisibility3(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(DIVISIBLE_BY(a, 2))
			print_hello(); // must execute

	   	if(!DIVISIBLE_BY(a, 2))
			print_impossible(); // should never execute
	}
}

void simple_divisibility4(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(!DIVISIBLE_BY(a, 2))
	   	{
			print_impossible(); // should never execute
		}
	}
}

void simple_divisibility5(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(DIVISIBLE_BY(a, 2))
	   	{
			print_hello(); // must execute
		}
	}
}

void simple_divisibility6(unsigned int x)
{
	if(x % 4 == 0)
	{
		if(x % 2 == 0)
			print_hello();
		else
			print_impossible();
	}
}

#define ALL_LO4_CLEAR(x) (((x) & 0b1111) == 0)
#define ALL_LO2_CLEAR(x) (((x) & 0b11) == 0)
#define AT_LEAST_ONE_LO4_SET(x) (!ALL_LO4_CLEAR(x))
#define AT_LEAST_ONE_LO2_SET(x) (!ALL_LO2_CLEAR(x))

// THEOREM: b3b2b1b0==0 -> b3b2b1b0==0
void cleared_bits0(unsigned int x)
{
	if(!ALL_LO4_CLEAR(x))
		return;
	// now all b3b2b1b0 == 0

	if(ALL_LO4_CLEAR(x))
		print_hello();
	else
		print_impossible();
}

// THEOREM: b3b2b1b0==0 -> b1b0==0
void cleared_bits1(unsigned int x)
{
	if(!ALL_LO4_CLEAR(x))
		return;
	// now all b3b2b1b0 == 0

	if(ALL_LO2_CLEAR(x))
		print_hello();
	else
		print_impossible();
}

// THEOREM: b3b2b1b0==0 -> b1b0==0
void cleared_bits2(unsigned int x)
{
	if(ALL_LO4_CLEAR(x))
	{
		if(ALL_LO2_CLEAR(x))
			print_hello();
		else
			print_impossible();
	}
}

// THEOREM: b3b2b1b0 == 0b1111 -> b3b2b1b0 != 0
void set_bits0(unsigned int x)
{
	if((x & 0b1111) != 0b1111)
		return;

	if(AT_LEAST_ONE_LO4_SET(x))
		print_hello();
	else
		print_impossible();
}

// THEOREM: b3b2b1b0 == 0b1111 -> b1b0 != 0
void set_bits1(unsigned int x)
{
	if((x & 0b1111) != 0b1111)
		return;

	if(AT_LEAST_ONE_LO2_SET(x))
		print_hello();
	else
		print_impossible();
}

// THEOREM: b3b2b1b0 == 0b1111 -> b1b0 == 0b11
void set_bits2(unsigned int x)
{
	if((x & 0b1111) == 0b1111)
	{
		if((x & 0b11) == 0b11)
			print_hello();
		else
			print_impossible();
	}
}

// THEOREM: 2 | (n + n)
void doubler_even0(unsigned int a)
{
	int b = a + a;

	if(DIVISIBLE_BY(b, 2))
	{
		print_hello();
	}
	else
	{
		print_impossible();
	}
}

// THEOREM: 10 < a < 1000000 -> 3a > 30
void tripler_greater_30(unsigned int a)
{
	if(! (a > 10 && a < 1000000) ) // [11, 1000000)
		return;

	int b = 3*a;

	if(b <= 30)
		print_impossible();
	else
		print_hello();
}

// THEOREM: x != 4, (2x - 5) / (x - 4) == 3 -> x == 7
// (from How To Prove It)
void htpi0(unsigned int x)
{
	if(x < 1000000 && x != 4) {
		int a = 2*x - 5;
		int b = x - 4;

		if(DIVISIBLE_BY(a, b) && a / b == 3)
		{
			if(x == 7)
			{
				print_hello();
			}
			else
			{
				print_impossible();
			}
		}
	}
}

// THEOREM: 9 cannot appear in the center position of the 3x3 magic triangle
// a b c
// d e f
// g h i
void magic_square(int a, int b, int c, int d, int e, int f, int g, int h, int i)
{
	e = 9;

	/* valid ranges */
	if(a < 1 || a > 9) return;
	if(b < 1 || b > 9) return;
	if(c < 1 || c > 9) return;
	if(d < 1 || d > 9) return;
	if(e < 1 || e > 9) return;
	if(f < 1 || f > 9) return;
	if(g < 1 || g > 9) return;
	if(h < 1 || h > 9) return;
	if(i < 1 || i > 9) return;

	/* they must be unique */
	if(a == b || a == c || a == d || a == e || a == f || a == g || a == h || a == i) return;
	if(b == c || b == d || b == e || b == f || b == g || b == h || b == i) return;
	if(c == d || c == e || c == f || c == g || c == h || c == i) return;
	if(d == e || d == f || d == g || d == h || d == i) return;
	if(e == f || e == g || e == h || e == i) return;
	if(f == g || f == h || f == i) return;
	if(g == h || g == i) return;
	if(h == i) return;

	/* rows */
	if(a+b+c != 15) return;
	if(d+e+f != 15) return;
	if(g+h+i != 15) return;

	/* columns */
	if(a+d+g != 15) return;
	if(b+e+h != 15) return;
	if(c+f+i != 15) return;

	/* diagonals */
	if(a+e+i != 15) return;
	if(c+e+g != 15) return;

	/* success (this is impossible with e = 9) */
	print_impossible();
}

// THEOREM: 6 cannot appear in a corner position of this magic triangle where each side sums to 9
// (because 1,2 would be needed twice along the two legs the corner connects)
/*
 *     a
 *    / \
 *   b   f
 *  /     \
 * c - d - e
 *
 *     2 
 *    / \
 *   6   4
 *  /     \
 * 1 - 5 - 3
 *
 */

void magic_triangle(int a, int b, int c, int d, int e, int f)
{
	a = 6;

	/* all within [1,6] */
	if(a < 1 || a > 6) return;
	if(b < 1 || b > 6) return;
	if(c < 1 || c > 6) return;
	if(d < 1 || d > 6) return;
	if(e < 1 || e > 6) return;
	if(f < 1 || f > 6) return;

	/* unique */
	if(a == b || a == c || a == d || a == e || a == f) return;
	if(b == c || b == d || b == e || b == f) return;
	if(c == d || c == e || c == f) return;
	if(d == e || d == f) return;
	if(e == f) return;

	/* all legs sum to 9 */
	if(a+b+c != 9) return;
	if(c+d+e != 9) return;
	if(a+f+e != 9) return;

	/* success! (this is impossible with a = 6) */
	print_impossible();
}

int main(int ac, char **av)
{
	int i;

	for(i=0; i<1000008; ++i)
		htpi0(i);

	return 0;
}
