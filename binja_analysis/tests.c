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

int main(int ac, char **av)
{
	fizzbuzz();
	print_2path(5);
	print_2path(15);
	return 0;
}
