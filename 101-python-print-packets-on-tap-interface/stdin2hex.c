#include <stdio.h>		/* perror(), printf(), fprintf() */
#include <string.h>		/* strcpy() */

#include <unistd.h>		/* read(), close(), STDIN_FILENO */

void dump_bytes(unsigned char *buf, int len, unsigned int addr)
{
	int i, j;
	char ascii[17];
	for(i=0; i<len; addr+=16) {
		strcpy(ascii, "................");
		printf("%08X: ", addr);
		for(j=0; j<16; j++, i++) {
			if(i < len) {
				printf("%02X ", buf[i]);
				if(buf[i]>=' ' && buf[i]<'~')
					ascii[j] = buf[i];
			}
			else {
				printf("   ");
				ascii[j] = ' ';
			}
		}
		printf(" %s\n", ascii);
	}
}

int main(int argc, char* argv[])
{
    int fd, nbytes;
    char buf[1600];

    while (1)
    {
        nbytes = read(STDIN_FILENO, buf, sizeof(buf));
        if(nbytes == 0)
        	break;

        dump_bytes(buf, nbytes, 0);
        printf("\n");
    }
    return 0;
}
