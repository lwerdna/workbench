/* dup2(A, B) won't just make B describe A's described file, it will make all other descriptors of B
   do the same.

                     +-------------+
[0] ---------------> |             |
[1] ---------------> | /dev/pts/13 |
[2] ---------------> |             |
                     +-------------+
                     +-------------+
[3] ---------------> | myfile.txt  | 
                     +-------------+

dup(3, 0)

                     +-------------+
[0] ---------------> |             |
[1] ---------------> | myfile.txt  |
[2] ---------------> |             |
[3] ---------------> |             |
                     +-------------+
*/

#include <stdio.h>

#include <fcntl.h>
#include <unistd.h>

void cool(void)
{
	char buf[4096];
	char fpath[1024];

	for(int i=0; i<256; ++i)
	{
		sprintf(fpath, "/proc/self/fd/%d", i);

		int rc = readlink(fpath, buf, 4096);
		if (rc >= 0)
			printf("%d: %s\n", i, buf);
	}
}

int main(int ac, char **av)
{
	int rc;

	cool();

	int fd = open("test.txt", O_WRONLY|O_CREAT, 0600);
	printf("fd: %d\n", fd);

	dup2(fd, STDIN_FILENO);

	cool();

	close(fd);

	return 0;
}
