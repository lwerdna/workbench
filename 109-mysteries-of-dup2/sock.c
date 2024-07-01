#include <stdio.h>

#include <unistd.h> // for close(), etc.
#include <sys/socket.h> // for struct sockaddr, etc.

int main(int ac, char **av)
{
	int fd = -1;

	fd = socket(PF_INET, SOCK_STREAM, 0);

	show_fds();
	dup2(fd, STDIN_FILENO);
	printf("--------\n");
	show_fds();

	cleanup:
		if (fd != -1)
			close(fd);

	return 0;
}
