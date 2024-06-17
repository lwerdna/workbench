#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
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

unsigned long long get_module_base(pid_t pid, char *module_name)
{
	FILE *fd;
	char fpath[128];
	char line[1024];
	unsigned long long addr = -1;

	snprintf(fpath, sizeof(fpath)-1, "/proc/%d/maps", pid);

	fd = fopen(fpath, "r");

	// since the entries are sorted, the first line that contains the library
	// name will have the base address at the front, like:
	// "7ffff7fc3000-7ffff7fc5000 r--p 00000000 103:02 10904444                  /usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"
	while (fgets(line, sizeof(line), fd)) {
		// printf("line: %s\n", line);
		if (strstr(line, module_name)) {
			addr = strtoull(line, NULL, 16);
			break;
		}
	}

	fclose(fd);

	return addr;
}

/* just like get_module_base() but also requires "r-xp" in line */
int get_module_executable_range(pid_t pid, char *module_name, uintptr_t *start, uintptr_t *end)
{
	int rc = -1;
	FILE *fd;
	char fpath[128];
	char line[1024];
	unsigned long long addr = -1;

	snprintf(fpath, sizeof(fpath)-1, "/proc/%d/maps", pid);

	fd = fopen(fpath, "r");

	while (fgets(line, sizeof(line), fd)) {
		if (strstr(line, module_name) && strstr(line, " r-xp ")) {
			*start = strtoull(line, NULL, 16);
			*end = strtoull(strstr(line, "-") + 1, NULL, 16);
			rc = 0;
			break;
		}
	}

	if (fd != NULL)
		fclose(fd);

	return rc;
}

int get_executable_name(pid_t pid, char *result)
{
	FILE *fd;
	char fpath[128];
	char fpath2[4096];
	memset(fpath2, '\0', sizeof(fpath2));

	snprintf(fpath, sizeof(fpath)-1, "/proc/%d/exe", pid);

	// NB: readlink() does not append a null byte to buf
	if (readlink(fpath, fpath2, sizeof(fpath2)) != -1) {
		int i = 0;
		if (strstr(fpath2, "/")) {
			for (i=strlen(fpath2)-1; fpath2[i] != '/'; i--);
			i += 1;
		}
		
		strcpy(result, fpath2+i);
		return 0;
	}

	return -1;
}

int main(int ac, char *av[])
{
	int rc, iret;
	int status;
	long lret;
	uintptr_t addr, lo, hi;

	pid_t pid;
	char *libname = "ld-linux-x86-64.so.2";
	char exe_name[1024];

	pid = atoi(av[1]);
	printf("Trying to find library \"%s\" in process %d\n", libname, pid);

	addr = get_module_base(pid, libname);
	if (addr != -1)
		printf("Found at: 0x%" PRIxPTR "\n", addr);

	if (get_executable_name(pid, exe_name) == 0) {
		printf("Got executable name: %s\n", exe_name);
	}

	iret = get_module_executable_range(pid, exe_name, &lo, &hi);
	if (iret == 0)
		printf("Got executable address range: [0x%" PRIxPTR ", 0x%" PRIxPTR ")\n", lo, hi);

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
