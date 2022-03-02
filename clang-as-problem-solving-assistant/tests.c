/* Test clang/llvm's insight into problems

Functions are written so logic paths which would defy a claim or theorem call print_impossible().
Then, presence of print_impossible() post optimization indicates clang/llvm failed to acquire insight.

FAILS means clang/llvm failed to eliminate the print_impossible()
SUCCEEDS means clang/llvm did eliminate the print_impossible() call

*/

#ifdef INCLUDE_STDIO
#include <stdio.h>
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

// SUCCEEDS
void simple_inequality0(int a)
{
	a &= 0b111;

	if(a > 10)
		print_impossible();
	else
		print_hello();
}

// THEOREM: n>20 -> n>10

// SUCCEEDS
void simple_inequality1(int n)
{
	if(n <= 20)
		return;

	if(n <= 10)
		print_impossible();
	else
		print_hello();
}

#define DIVISIBLE_BY(a,b) ((a) % (b) == 0)

// THEOREM: 4|n -> 2|n

// FAILS
void simple_divisibility0(unsigned int a)
{
	if(!DIVISIBLE_BY(a, 4))
	   	return;

   	if(DIVISIBLE_BY(a, 2))
		print_hello(); // could execute
   	else
		print_impossible(); // should never execute
}

// FAILS
void simple_divisibility1(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(DIVISIBLE_BY(a, 2))
			print_hello(); // could execute
	   	else
			print_impossible(); // should never execute
	}
}

// FAILS
void simple_divisibility2(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(DIVISIBLE_BY(a, 2))
			while(0); // could execute
	   	else
			print_impossible(); // should never execute
	}
}

// FAILS
void simple_divisibility3(unsigned int a)
{
	if(DIVISIBLE_BY(a, 4))
	{
	   	if(DIVISIBLE_BY(a, 2))
			print_hello(); // could execute

	   	if(!DIVISIBLE_BY(a, 2))
			print_impossible(); // should never execute
	}
}

// SUCCEEDS
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
			print_hello(); // could execute
		}
	}
}

#define LOW_4_BITS_CLEAR(x) (((x) & 0b1111) == 0)
#define LOW_2_BITS_CLEAR(x) (((x) & 0b11) == 0)

// THEOREM: b3b2b1b0==0 -> b1b0==0

// FAILS to eliminate print_impossible()
void cleared_bits0(unsigned int x)
{
	if(!LOW_4_BITS_CLEAR(x))
		return;

	if(LOW_2_BITS_CLEAR(x))
		print_hello();
	else
		print_impossible();
}

// SUCCEEDS
void cleared_bits1(unsigned int x)
{
	if(!LOW_4_BITS_CLEAR(x))
		return;

	if(LOW_2_BITS_CLEAR(x))
		while(0);
	else
		print_impossible();
}

// FAILS
void cleared_bits2(unsigned int x)
{
	if(!LOW_4_BITS_CLEAR(x))
		return;

	if(LOW_2_BITS_CLEAR(x))
		print_hello();

	if(!LOW_2_BITS_CLEAR(x))
		print_impossible();
}

// SUCCEEDS
void cleared_bits3(unsigned int x)
{
	if(!LOW_4_BITS_CLEAR(x))
		return;

	if(!LOW_2_BITS_CLEAR(x))
		print_impossible();
}

// FAILS
void cleared_bits4(unsigned int x)
{
	if(LOW_4_BITS_CLEAR(x))
	{
		if(LOW_2_BITS_CLEAR(x))
		{
			print_hello();
		}
		else
		{
			if(!LOW_2_BITS_CLEAR(x))
			{
				print_impossible();
			}
		}
	}
}

// FAILS
void cleared_bits5(unsigned int x)
{
	if(LOW_4_BITS_CLEAR(x))
	{
		if(!LOW_2_BITS_CLEAR(x))
		{
			print_impossible();
		}
		else
		{
			print_hello();
		}
	}
}

// THEOREM: 2 | (n + n)

// SUCCEEDS 
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

// SUCCEEDS
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

// FAILS
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
//
// FAILS
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

	/* success */
	print_impossible();
}

/*
 *     a
 *    / \
 *   b   f
 *  /     \
 * c - d - e
 *
 */

void magic_triangle(int a, int b, int c, int d, int e, int f)
{
	a = 6;

	if(a < 1 || a > 6) return;
	if(b < 1 || b > 6) return;
	if(c < 1 || c > 6) return;
	if(d < 1 || d > 6) return;
	if(e < 1 || e > 6) return;
	if(f < 1 || f > 6) return;

	if(a == b || a == c || a == d || a == e || a == f) return;
	if(b == c || b == d || b == e || b == f) return;
	if(c == d || c == e || c == f) return;
	if(d == e || d == f) return;
	if(e == f) return;

	if(a+b+c != 9) return;
	if(c+d+e != 9) return;
	if(a+f+e != 9) return;

	print_impossible();
}

int main(int ac, char **av)
{
	int i;

	for(i=0; i<1000008; ++i)
		htpi0(i);

	return 0;
}
