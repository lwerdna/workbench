#include <stdio.h>
#include <unistd.h>

int show_fds(void)
{
	char buf[4096];
	char fpath[1024];

	for(int i=0; i<256; ++i)
	{
		sprintf(fpath, "/proc/self/fd/%d", i);

		// From `man 2 readlink`:
		// > readlink() does not append a null byte to buf
		int rc = readlink(fpath, buf, 4096);
		if (rc >= 0)
		{
			buf[rc] = '\0';
			printf("%d: %s\n", i, buf);
		}
	}

	return 0;
}
