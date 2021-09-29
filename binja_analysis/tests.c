/* tests
 * gcc tests.c -o tests
 */

#include <stdio.h>

void print_2path(int a)
{
	if(a<10) {
		printf("less\n");
	}
	else {
		printf("more\n");
	}
}

/* Write a program that prints the numbers from 1 to 100. But for multiples of three print “Fizz” instead of the number and for the multiples of five print “Buzz”. For numbers which are multiples of both three and five print “FizzBuzz”.*/
void fizzbuzz(void)
{
	for(int i=1; i<=100; ++i) {
		if(i%15 == 0) printf("FizzBuzz\n");
		else if(i%3 == 0) printf("Fizz\n");
		else if(i%5 == 0) printf("Buzz\n");
		else printf("%d\n", i);
	}
}

int collatz_message(char *message, int n)
{
	if(n % 2) {
		/* is odd */
		n = 3*n + 1;
	}
	else {
		/* is even */
		n = n / 2;
	}

	if(message)
		printf("%s: %d", message, n);

	return n;
}

int main(int ac, char **av)
{
	fizzbuzz();
	print_2path(5);
	print_2path(15);
	return 0;
}
