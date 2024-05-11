/* stdin/stdout/stderr are separate file descriptors that all refer to the same pseudo terminal slave (pts)
0: /dev/pts/40
1: /dev/pts/40
2: /dev/pts/40

*/
#include <stdio.h>

#include <fcntl.h>
#include <unistd.h>

int main(int ac, char **av)
{
	int rc;
	char buf[4096];

	rc = readlink("/proc/self/fd/0", buf, 4096);
	if (rc >= 0)
		printf("0: %s\n", buf);

	rc = readlink("/proc/self/fd/1", buf, 4096);
	if (rc >= 0)
		printf("1: %s\n", buf);

	rc = readlink("/proc/self/fd/2", buf, 4096);
	if (rc >= 0)
		printf("2: %s\n", buf);

	rc = readlink("/proc/self/fd/3", buf, 4096);
	if (rc >= 0)
		printf("3: %s\n", buf);

	// could we read() on stdout?
	printf("testing a read() on stdout...\n");
	read(STDOUT_FILENO, buf, 1);
	printf("you typed: %c\n", buf[0]);

	printf("testing a read() on stderr...\n");
	read(STDERR_FILENO, buf, 1);
	printf("you typed: %c\n", buf[0]);

	return 0;
}
