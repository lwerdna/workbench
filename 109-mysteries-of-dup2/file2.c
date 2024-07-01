#include <stdio.h>
#include <string.h>

#include <fcntl.h>
#include <unistd.h>

int main(int ac, char **av)
{
	int rc;

	int fdA = open("a.txt", O_WRONLY|O_CREAT, 0600);
	printf("a.txt fd: %d\n", fdA);
	dup(fdA);
	dup(fdA);
	dup(fdA);
	int fdB = open("b.txt", O_WRONLY|O_CREAT, 0600);
	printf("b.txt fd: %d\n", fdB);
	dup(fdB);
	dup(fdB);
	int tmp = dup(fdB);

	show_fds();

	dup2(fdA, fdB);
	printf("--------\n");
	show_fds();

	const char *msg = "b is still open!\n";
	write(tmp, msg, strlen(msg)+1);

	close(fdA);
	close(fdB);

	return 0;
}
