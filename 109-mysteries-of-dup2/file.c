#include <stdio.h>

#include <fcntl.h>
#include <unistd.h>

int main(int ac, char **av)
{
	int rc;

	write(STDIN_FILENO, "write 0\n", 8);
	write(STDOUT_FILENO, "write 1\n", 8);
	write(STDERR_FILENO, "write 2\n", 8);

	int fd = open("test.txt", O_WRONLY|O_CREAT, 0600);
	printf("fd: %d\n", fd);

	show_fds();
	dup2(fd, STDIN_FILENO);
	printf("--------\n");
	show_fds();

	write(STDIN_FILENO, "write 0\n", 8);
	write(STDOUT_FILENO, "write 1\n", 8);
	write(STDERR_FILENO, "write 2\n", 8);

	close(fd);

	return 0;
}
