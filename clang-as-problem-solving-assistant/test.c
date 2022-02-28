#include <stdio.h>

__attribute__((noinline))
void print_yes()
{
	printf("YES\n");
}

__attribute__((noinline))
void print_no()
{
	printf("NO\n");
}

void foo0(int a)
{
	if(a > 10) {
		printf("greater than 10\n");
	}
	else {
		printf("less than 10\n");
	}
}

void foo1(int a)
{
	a &= 0b111;

	if(a > 10) {
		printf("greater than 10\n");
	}
	else {
		printf("less than 10\n");
	}
}

void foo2(int a)
{
	if(a % 4)
		return;

	if(a % 2)
		printf("NO\n");
	else
		printf("YES\n");
}

void foo3(int a)
{
	if(a & 0b11)
		return;

	// then (a & 0b11) == 0
	//  and (a & 0b1) == 0
	if(a & 0b1)
		printf("NO\n");
	else
		printf("YES\n");
}

void foo4(int a)
{
	int b = a + a;

	if(b % 2)
		print_no();
	else
		print_yes();
}

void foo5(int a)
{
	if(! (a > 10 && a < 1000000) ) // [11, 1000000)
		return;

	int b = 3*a;

	if(b <= 30)
		print_no();
	else
		print_yes();
}

void foo6(int x)
{
	if(x < 1000000 && x != 4) {
		int a = 2*x - 5;
		int b = x - 4;

		if(a % b == 0 && a / b == 3) {
			if(x == 7) {
				print_yes();
			}
			else {
				print_no();
			}
		}
	}
}

/*
 a b c
 d e f
 g h i
 */
void foo7(int a, int b, int c, int d, int e, int f, int g, int h, int i)
{
	e = 9;

	/* valid ranges */
	if(a < 1 || a > 9) { print_no(); return; }
	if(b < 1 || b > 9) { print_no(); return; }
	if(c < 1 || c > 9) { print_no(); return; }
	if(d < 1 || d > 9) { print_no(); return; }
	if(e < 1 || e > 9) { print_no(); return; }
	if(f < 1 || f > 9) { print_no(); return; }
	if(g < 1 || g > 9) { print_no(); return; }
	if(h < 1 || h > 9) { print_no(); return; }
	if(i < 1 || i > 9) { print_no(); return; }

	/* they must be unique */
	if(a == b || a == c || a == d || a == e || a == f || a == g || a == h || a == i) { print_no(); return; }
	if(b == c || b == d || b == e || b == f || b == g || b == h || b == i) { print_no(); return; }
	if(c == d || c == e || c == f || c == g || c == h || c == i) { print_no(); return; }
	if(d == e || d == f || d == g || d == h || d == i) { print_no(); return; }
	if(e == f || e == g || e == h || e == i) { print_no(); return; }
	if(f == g || f == h || f == i) { print_no(); return; }
	if(g == h || g == i) { print_no(); return; }
	if(h == i) { print_no(); return; }

	/* rows */
	if(a+b+c != 15) { print_no(); return; }
	if(d+e+f != 15) { print_no(); return; }
	if(g+h+i != 15) { print_no(); return; }

	/* columns */
	if(a+d+g != 15) { print_no(); return; }
	if(b+e+h != 15) { print_no(); return; }
	if(c+f+i != 15) { print_no(); return; }

	/* diagonals */
	if(a+e+i != 15) { print_no(); return; }
	if(c+e+g != 15) { print_no(); return; }

	/* success */
	print_yes();
}

/*
 *     a
 *    / \
 *   b   f
 *  /     \
 * c - d - e
 *
 */

void foo8(int a, int b, int c, int d, int e, int f)
{
	a = 6;

	if(a < 1 || a > 6) { print_no(); return; }
	if(b < 1 || b > 6) { print_no(); return; }
	if(c < 1 || c > 6) { print_no(); return; }
	if(d < 1 || d > 6) { print_no(); return; }
	if(e < 1 || e > 6) { print_no(); return; }
	if(f < 1 || f > 6) { print_no(); return; }

	if(a == b || a == c || a == d || a == e || a == f) { print_no(); return; }
	if(b == c || b == d || b == e || b == f) { print_no(); return; }
	if(c == d || c == e || c == f) { print_no(); return; }
	if(d == e || d == f) { print_no(); return; }
	if(e == f) { print_no(); return; }

	if(a+b+c != 9) { print_no(); return; }
	if(c+d+e != 9) { print_no(); return; }
	if(a+f+e != 9) { print_no(); return; }

	print_yes();
}

int main(int ac, char **av)
{
	int i;

	for(i=0; i<1000008; ++i)
		foo6(i);

	return 0;
}
