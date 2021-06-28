#include <stdio.h>

extern int MySuperComputation(int, int);

int main(int ac, char **av) {
	printf("5+6=%d\n", MySuperComputation(5, 6));
	return 0;
}
