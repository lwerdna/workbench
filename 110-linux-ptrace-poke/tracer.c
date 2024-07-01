#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>

#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

void hexdump(uint8_t *data, size_t size, uintptr_t addr)
{
	char ascii[17];
	for (int i = 0; i < size; ++i) {
		if (i % 16 == 0)
			printf("%" PRIxPTR ": ", addr+i); // print address
		printf("%02X ", ((unsigned char*)data)[i]); // print byte
		ascii[i % 16] = (data[i]>=' ' && data[i]<='~') ? (char)data[i] : '.'; // fill ascii
		if (i==size-1 || (i+1) % 16 == 0) {
			for (int j=15-(i%16); j>0; --j) // advance to ascii
				printf("   ");
			ascii[i%16 + 1] = '\0';
			printf(" %s\n", ascii); // print ascii
		}
	}
}

int read_mem(pid_t pid, uintptr_t addr, size_t size, uint8_t *output)
{
	for(int i=0; i<size; i += sizeof(long)) {
		long lret = ptrace(PTRACE_PEEKDATA, pid, addr+i, 0);
		if (lret == -1) {
			perror("ptrace(PTRACE_PEEKDATA, ...)");
			exit(1);
		}
		*(long *)(output + i) = lret;
	}

	return 0;
}

int main(int ac, char *av[])
{
	int rc;
	pid_t pid;
	int status;
	long lret;
	uintptr_t addr;

	if(ac < 3) {
		printf("usage to read:\n");
		printf("	%s <pid> <address>\n", av[0]);
		printf("usage to write:\n");
		printf("	%s <pid> <address> <value>\n", av[0]);
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

	#define DUMPSZ 256+12
	uint8_t buf[DUMPSZ + sizeof(long)];
	rc = read_mem(pid, addr, DUMPSZ, buf);
	if (rc != 0) {
		exit(1);
	}
	hexdump(buf, DUMPSZ, addr);

	// sizeof(long) is size_t, printed with zu
	printf("sizeof(long)==%zu\n", sizeof(long));

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
