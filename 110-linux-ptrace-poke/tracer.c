#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>

#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

int main(int ac, char *av[])
{
	int rc;
	pid_t pid;
	int status;
    long lret;
	uintptr_t addr;

    if(ac < 3) {
        printf("usage to read:\n");
        printf("    %s <pid> <address>\n", av[0]);
        printf("usage to write:\n");
        printf("    %s <pid> <address> <value>\n", av[0]);
        exit(1);
    }

    pid = atoi(av[1]);
    addr = strtoull(av[2], NULL, 16);

    printf("attaching to process pid=%d\n", pid);
    rc = ptrace(PTRACE_ATTACH, pid, 0, 0);
    if (rc == -1) {
    	perror("ptrace(PTRACE_ATTACH, ...)");
    	exit(1);
    }

    printf("waiting on pid=%d\n", pid);
    rc = waitpid(pid, &status, 0);
    if (rc == -1) {
		perror("waitpid()");
		exit(1);
    }

	printf("reading from 0x%" PRIxPTR "\n", addr);
    lret = ptrace(PTRACE_PEEKDATA, pid, addr, 128);
    if (lret == -1) {
    	perror("ptrace(PTRACE_PEEKDATA, ...)");
    	exit(1);
    }
	printf("read: 0x%lx\n", lret);

	printf("sizeof(long)==%d\n", sizeof(long));

	if (ac > 3) {
    	long value = strtoul(av[3], NULL, 16);
		printf("writing 0x%lx to 0x%" PRIxPTR "\n", value, addr);
	    lret = ptrace(PTRACE_POKEDATA, pid, addr, value);
	    if (lret == -1) {
	    	perror("ptrace(PTRACE_POKEDATA, ...)");
	    	exit(1);
	    }
	}

	printf("detaching from pid=%d\n", pid);
    lret = ptrace(PTRACE_DETACH, pid, 0, 0);
    if (lret == -1) {
    	perror("ptrace(PTRACE_PEEKDATA, ...)");
    	exit(1);
    }

    return 0;
}
