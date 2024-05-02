// open a tap device and hook up stdin/stdout
//
// stdin -> writes packet to tap device
// tap devices packet -> written to stdout

#include <stdint.h>

#include <fcntl.h>     /* O_RDWR */
#include <stdio.h>     /* perror(), printf(), fprintf() */
#include <stdlib.h>    /* exit(), malloc(), free() */
#include <string.h>    /* memset(), memcpy() */
#include <sys/ioctl.h> /* ioctl() */
#include <unistd.h>    /* read(), close(), STDOUT_FILENO */

/* includes for struct ifreq, etc */
#include <linux/if.h>
#include <linux/if_tun.h>
#include <sys/socket.h>
#include <sys/types.h>

int tap_open(char* devname)
{
    int fd;
    if ((fd = open("/dev/net/tun", O_RDWR)) == -1) {
        perror("open /dev/net/tun");
        exit(1);
    }

    struct ifreq ifr;
    memset(&ifr, 0, sizeof(ifr));
    // IFF_TAP, IFF_TUN
    // IFF_NO_PI
    ifr.ifr_flags = IFF_TAP;
    ifr.ifr_flags |= IFF_NO_PI; // IFF_NO_PI - Do not provide packet information (4 byte header)
    strncpy(ifr.ifr_name, devname, IFNAMSIZ); // devname = "tun0" or "tun1", etc

    /* ioctl will use ifr.if_name as the name of TUN
     * interface to open: "tun0", etc. */
    int err;
    if ((err = ioctl(fd, TUNSETIFF, (void*)&ifr)) == -1) {
        perror("ioctl TUNSETIFF");
        close(fd);
        exit(1);
    }

    /* After the ioctl call the fd is "connected" to tun device specified
     * by devname ("tun0", "tun1", etc)*/
    return fd;
}

int main(int argc, char* argv[])
{
    int fd_tap, n_read, n_written;
    char buf[1600];

	char *name = "tap0";
	if(argc > 1)
		name = argv[1];

    fd_tap = tap_open(name); /* devname = ifr.if_name = "tap0" */
    //printf("Device %s opened\n", name);

	if(fd_tap >= FD_SETSIZE)
	{
		printf("returned file descriptor too large for select()\n");
		exit(1);
	}

    while(1)
    {
    	printf("top\n");

		struct timeval timeout;
		timeout.tv_sec = 1;
		timeout.tv_usec = 0;

		// from `man 2 select`:
		// Thus, if using select() within a loop, the sets must be reinitialized before each call.
		fd_set myset;
		FD_ZERO(&myset);
		FD_SET(STDIN_FILENO, &myset); // add STDIN to file set
		FD_SET(fd_tap, &myset); // add tuntap fd to file set
    	int max_fd = ((fd_tap > STDIN_FILENO) ? fd_tap : STDIN_FILENO) + 1;
    	int rc = select(max_fd, &myset, NULL, NULL, &timeout);
		if(rc == -1)
		{
			perror("select()");
			break;
		}

		if(rc == 0) // timeout
			continue;

		// STDIN -> tap
		if(FD_ISSET(STDIN_FILENO, &myset))
		{
	        n_read = read(STDIN_FILENO, buf, sizeof(buf));
        	n_written = write(fd_tap, buf, n_read);
	    }

	    // tap -> STDOUT
	    if(FD_ISSET(fd_tap, &myset))
	    {
	        n_read = read(fd_tap, buf, sizeof(buf));
        	n_written = write(STDOUT_FILENO, buf, n_read);
	    }

        if(n_read != n_written)
        {
        	perror("write()");
        	exit(1);
		}
    }

    return 0;
}
