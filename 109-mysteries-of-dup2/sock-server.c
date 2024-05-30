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

	show_fds();
	dup2(fd, STDIN_FILENO);
	printf("--------\n");
	show_fds();

	cleanup:
		if (fd != -1)
			close(fd);

	return 0;
}
