#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h> // exit(), etc.

#include <fcntl.h> // fcntl()
#include <unistd.h> // close()
#include <sys/errno.h>
#include <sys/socket.h>
#include <sys/select.h>
#include <arpa/inet.h> // inet_addr()
#include <netinet/in.h>

#define BLAST_SZ (FD_SETSIZE-16)
#define TIMEOUT_SEC 0

void printset(fd_set *set)
{
	int i;
	for(i=0; i<FD_SETSIZE; ++i)
		if(FD_ISSET(i, set))
			printf("%d is set\n", i);
}

int main(int ac, char **av)
{
	int rc = -1, i, j, max_fd;
	int port_cur, port_start, port_end;

	struct sockaddr_in saddr_in;

	fd_set fds_w;
	fd_set fds_e;

	uint32_t flags;
	
	struct conn_info {
		int sock;
		uint16_t port;
		struct sockaddr_in addr;
	};

	char *ip = (char *)"127.0.0.1";

	struct conn_info cinfos[BLAST_SZ];

	int num_ready;
	struct timeval timeout = {TIMEOUT_SEC, 1};

	socklen_t opt, opt_len;
	socklen_t sklt;

	/* scan parameters */
	port_start = 0;
	port_end = 65536;
	if(ac > 1) ip = av[1];
	if(ac > 2) port_start = atoi(av[2]);
	if(ac > 3) port_end = atoi(av[3]);
	printf("scanning %s ports [%d,%d)\n", ip, port_start, port_end);
		
	/* clear queue */
	for(i=0; i<BLAST_SZ; ++i)
		cinfos[i].sock = -1;

	/* loop over ports */
	port_cur = port_start;
	while(port_cur < port_end) {
		/* fill queue */
		for(i=0; i<BLAST_SZ && port_cur < port_end; ++i) {
			/* seek to empty slot */
			if(cinfos[i].sock != -1) {
				//printf("slot[%d] = {.port=%d} previously occupied\n", i, cinfos[i].port);
				continue;
			}

			/* connect() until EINPROGRESS */
			while(port_cur < port_end) {
				int sock;
				uint32_t flags;

				sock  = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
				if(sock == -1)
					{ printf("ERROR: socket()\n"); goto cleanup; }

				flags = fcntl(sock, F_GETFL, 0);
				fcntl(sock, F_SETFL, flags | O_NONBLOCK);
	
				memset(&saddr_in, 0, sizeof(saddr_in));
				saddr_in.sin_family = AF_INET;
				saddr_in.sin_addr.s_addr = inet_addr(ip);
				saddr_in.sin_port = htons(port_cur);

				rc = connect(sock, (struct sockaddr *)&saddr_in,
				  sizeof(saddr_in));

				if(rc == 0) {
					/* this happens on FreeBSD, despite the O_NONBLOCK */
					printf("port %d is open (immediate connect!)\n", port_cur);
				}
				else {
					if(errno == EINPROGRESS) {
						cinfos[i].sock = sock;
						cinfos[i].port = port_cur;
						cinfos[i].addr = saddr_in;

						//printf("slot[%d] = {.sock=%d, .port=%d} added\n",
						//  i, sock, port_cur);

						break;
					}
					else if(errno == ECONNREFUSED) {
						while(0);
					}
					else {
						printf("ERROR: connect(..., port=%d) (errno=%d)\n", port_cur, errno);
					};
				}

				close(sock);
				port_cur++;
			}

			port_cur++;
		}

		/* queue -> FD SET */
		//printf("loading queue into an FD_SET for select()\n");
		max_fd = 0;
		FD_ZERO(&fds_w);
		FD_ZERO(&fds_e);

		for(i=0; i<BLAST_SZ; ++i) {
			if(cinfos[i].sock == -1)
				continue;

			if(cinfos[i].sock > max_fd)
				max_fd = cinfos[i].sock;

			FD_SET(cinfos[i].sock, &fds_w);
			FD_SET(cinfos[i].sock, &fds_e);
			//printf("slot[%d] = {.sock=%d, .port=%d} added to FD_SET()\n",
			//  i, cinfos[i].sock, cinfos[i].port);
		}

		/* select() on them: ready for write means they connected */
		//printf("calling select(%d, ..., NULL, to)\n", max_fd+1);
		num_ready = select(max_fd+1, NULL, &fds_w, NULL, &timeout);

		if(num_ready < 0) { 
			printf("ERROR: select()\n"); goto cleanup;
		}
		else if(num_ready == 0) {
			//printf("select() says NONE are ready, clearing...\n");

			for(i=0; i<BLAST_SZ; ++i) {
				close(cinfos[i].sock);
				cinfos[i].sock = -1;
			}

			continue;
		}

		//printf("select() says %d are ready\n", num_ready);
	
		for(i=0; i<BLAST_SZ; ++i) {
			/* skip uninitialized or unset FD's */
			if(cinfos[i].sock == -1)
				continue;

			if(FD_ISSET(cinfos[i].sock, &fds_e) && !FD_ISSET(cinfos[i].sock, &fds_w)) {
				close(cinfos[i].sock);
				cinfos[i].sock = -1;
				continue;
			}
			
			/* neither set? next! */
			if(!FD_ISSET(cinfos[i].sock, &fds_w))
				continue;

			opt_len = sizeof(opt);
			j = getsockopt(cinfos[i].sock, SOL_SOCKET, SO_ERROR, &opt, &opt_len);
			if(j < 0) {
				printf("ERROR: getsockopt(sock=%d, port=%d)\n",
				  cinfos[i].sock, cinfos[i].port);
				goto cleanup;
			}

			switch(opt) {
				case 0:
					sklt = sizeof(saddr_in);
					if(getsockname(cinfos[i].sock, (struct sockaddr *)&saddr_in,
					  &sklt) || (sklt != sizeof(saddr_in))) {
						printf("ERROR: getsockname()\n");
						goto cleanup;
					}

					/* see http://sgros.blogspot.com/2013/08/tcp-client-self-connect.html */
					if(saddr_in.sin_port == cinfos[i].addr.sin_port &&
					  saddr_in.sin_addr.s_addr == cinfos[i].addr.sin_addr.s_addr) {
						printf("self-connected detected on port %d\n",
						  saddr_in.sin_port);
						break;
					}

					printf("port %d is open!\n", cinfos[i].port);

					break;
				case EINPROGRESS:
					printf("slot[%d] = {.port=%d} still in progress\n", i, cinfos[i].port);
					continue;
				case ECONNREFUSED:
				case ETIMEDOUT:
					break;
				default:
					printf("slot[%d] = {.port=%d} removing (SOCK_ERR=%d)\n",
					  i, cinfos[i].port, opt);
			}

			close(cinfos[i].sock);
			cinfos[i].sock = -1;
		}

		//printf("about to continue, port_cur=%d, port_end=%d\n", port_cur, port_end);
	} // closes the while(1) connect/select block
	
	rc = 0;
	cleanup:
	return rc;
}
