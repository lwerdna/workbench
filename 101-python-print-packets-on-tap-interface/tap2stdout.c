// open a tap device and stream its output to our stdout
//
// https://stackoverflow.com/questions/1003684/how-to-interface-with-the-linux-tun-driver/35735842

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
    struct ifreq ifr;
    int fd, err;

    if ((fd = open("/dev/net/tun", O_RDWR)) == -1) {
        perror("open /dev/net/tun");
        exit(1);
    }
    memset(&ifr, 0, sizeof(ifr));
    // IFF_TAP, IFF_TUN
    // IFF_NO_PI
    ifr.ifr_flags = IFF_TAP;
    ifr.ifr_flags |= IFF_NO_PI; // IFF_NO_PI - Do not provide packet information (4 byte header)
    strncpy(ifr.ifr_name, devname, IFNAMSIZ); // devname = "tun0" or "tun1", etc

    /* ioctl will use ifr.if_name as the name of TUN
     * interface to open: "tun0", etc. */
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
    int fd, n_read, n_written;
    char buf[1600];

	char *name = "tap0";
	if(argc > 1)
		name = argv[1];

    fd = tap_open(name); /* devname = ifr.if_name = "tap0" */
    //printf("Device %s opened\n", name);

    while(1)
    {
        n_read = read(fd, buf, sizeof(buf));
        //printf("Read %d bytes from tap0\n", n_read);

        n_written = write(STDOUT_FILENO, buf, n_read);

        if(n_read != n_written)
        {
        	perror("write()");
        	exit(1);
		}
    }
    return 0;
}
