#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <dlfcn.h>

#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/user.h>
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
	long lret;

	for (int i=0; i<size; i += sizeof(long)) {
		lret = ptrace(PTRACE_PEEKDATA, pid, addr+i, 0);
		if (lret == -1)
			return -1;
		*(long *)(output + i) = lret;
	}

	return 0;
}

int write_mem(pid_t pid, uintptr_t addr, uint8_t *data, size_t size)
{
	long lret;

	for (int i=0; i<size; i += sizeof(long)) {
		printf("writing %zu bytes to address 0x%" PRIxPTR "\n", sizeof(long), addr+i);
		lret = ptrace(PTRACE_POKEDATA, pid, addr+i, *(unsigned long *)(data + i));
		if (lret == -1)
			return -1;
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
		//printf("looking for \"%s\" in line: %s", module_name, line);
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

int get_module_for_address(pid_t pid, uintptr_t addr, char *result)
{
	int i, rc = -1;
	FILE *fd;
	char fpath[128];
	char line[1024];
	uintptr_t lo, hi;

	snprintf(fpath, sizeof(fpath)-1, "/proc/%d/maps", pid);

	fd = fopen(fpath, "r");

	while (fgets(line, sizeof(line), fd)) {
		for (i=strlen(line)-1; line[i]==' ' || line[i]=='\t' || line[i] == '\n'; i--)
			line[i] = '\0';
		// chomp trailing " (deleted)"
		if (strlen(line) >= 10 && !strcmp(line+strlen(line)-10, " (deleted)"))
			line[strlen(line)-10] = '\0';

		lo = strtoull(line, NULL, 16);
		hi = strtoull(strstr(line, "-") + 1, NULL, 16);
		//printf("[0x%" PRIxPTR ", 0x%" PRIxPTR ") vs. 0x%" PRIxPTR "\n", lo, hi, addr);
		if (addr >= lo && addr < hi) {
			// find rightmost token (the module name)
			for (i=strlen(line)-1; line[i] != ' '; i--);
			strcpy(result, line+i+1);
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

uintptr_t get_executing_address(pid_t pid)
{
    #ifdef __x86_64__
    struct user_regs_struct regs;
    #endif
    #ifdef __arm__
    struct user_regs regs;
    #endif

	int rc = ptrace(PTRACE_GETREGS, pid, NULL, &regs);
	if (rc == -1) {
		perror("ptrace(PTRACE_GETREGS, ...)");
		exit(1);
	}

	#ifdef __x86_64__
	printf("rip = 0x%llX\n", regs.rip);
	return regs.rip;
	#endif
	#ifdef __arm__
	printf("pc = 0x%" PRIxPTR "\n", regs.pc);
	return regs.pc;
	#endif
}

char *signal_to_name(int sig)
{
	switch(sig) {
		case SIGHUP: return "SIGHUP";
		case SIGINT: return "SIGINT";
		case SIGQUIT: return "SIGQUIT";
		case SIGILL: return "SIGILL";
		case SIGTRAP: return "SIGTRAP";
		case SIGABRT: return "SIGABRT";
		//case SIGIOT: return "SIGIOT";
		case SIGBUS: return "SIGBUS";
		case SIGFPE: return "SIGFPE";
		case SIGKILL: return "SIGKILL";
		case SIGUSR1: return "SIGUSR1";
		case SIGSEGV: return "SIGSEGV";
		case SIGUSR2: return "SIGUSR2";
		case SIGPIPE: return "SIGPIPE";
		case SIGALRM: return "SIGALRM";
		case SIGTERM: return "SIGTERM";
		case SIGSTKFLT: return "SIGSTKFLT";
		case SIGCHLD: return "SIGCHLD";
		case SIGCONT: return "SIGCONT";
		case SIGSTOP: return "SIGSTOP";
		case SIGTSTP: return "SIGTSTP";
		case SIGTTIN: return "SIGTTIN";
		case SIGTTOU: return "SIGTTOU";
		case SIGURG: return "SIGURG";
		case SIGXCPU: return "SIGXCPU";
		case SIGXFSZ: return "SIGXFSZ";
		case SIGVTALRM: return "SIGVTALRM";
		case SIGPROF: return "SIGPROF";
		case SIGWINCH: return "SIGWINCH";
		case SIGIO: return "SIGIO";
		case SIGPWR: return "SIGPWR";
		case SIGSYS: return "SIGSYS";
		default: return "UNKNOWN";
	}
}

// return:
// 0 - child still running
//
int wait_debuggee(pid_t pid)
{
	int rc, status;

	#ifdef __x86_64__
    struct user_regs_struct regs;
    #endif
    #ifdef __arm__
    struct user_regs regs;
    #endif

	printf("waiting on pid=%d\n", pid);
	rc = waitpid(pid, &status, 0);
	if (rc == -1) {
		return -1;
	}

	if (WIFEXITED(status)) {
		printf("child exited with status %d\n", WEXITSTATUS(status));
		return -1;
	}

	if (WIFSIGNALED(status)) {
		printf("child terminated by signal %d (%s)\n",
			WTERMSIG(status), signal_to_name(WTERMSIG(status)));
		return -1;
	}

	if (WIFSTOPPED(status)) {
		int ptrace_event = status >> 16;
		int signal = WSTOPSIG(status);

		if (ptrace_event == PTRACE_EVENT_STOP) {
			if (signal == SIGSTOP || signal == SIGTSTP || signal == SIGTTIN || signal == SIGTTOU) {
				printf("injectee entered group-stop PTRACE_EVENT_STOP (signal: %d)\n", signal);
					ptrace(PTRACE_LISTEN, pid, NULL, NULL);
			} else {
				printf("injectee entered non-group-stop PTRACE_EVENT_STOP (signal: %d)\n", signal);
				ptrace(PTRACE_SYSCALL, pid, NULL, 0);
			}
		}
		else {
			if (signal == (SIGTRAP | 0x80)) {
				printf("injectee entered/exited syscall\n");
				//ptrace(PTRACE_SYSCALL, pid, NULL, 0);
			} else {
				printf("injectee received signal (signal: %d (%s))\n",
					signal, signal_to_name(signal));
				//ptrace(PTRACE_SYSCALL, pid, NULL, signal);
			}
		}
		//printf("child stopped by signal %d (%s)\n",
		//	WSTOPSIG(status), signal_to_name(WSTOPSIG(status)));
	}
	else
	{
		printf("waitpid(), but don't know how to interpret status 0x%X\n", status);
		return -1;
	}

	ptrace(PTRACE_GETREGS, pid, NULL, &regs);
	printf("target stopped at 0x%llx\n", regs.rip);

	return 0;
}

int main(int ac, char *av[])
{
	int rc, iret;
	int status;
	long lret;
	uintptr_t addr, lo, hi;

	#ifdef __x86_64__
    struct user_regs_struct regs, regs_old;
    #endif
    #ifdef __arm__
    struct user_regs regs, regs_old;
    #endif

	pid_t pid;
	char module_name[1024];

	/* resolve libc offsets */
	addr = get_module_base(getpid(), "libc");
	printf("(injector) libc base: 0x%" PRIxPTR "\n", addr);
	printf("(injector) address of raise(): %p\n", raise);
	printf("(injector) address of dlopen(): %p\n", dlopen);
	uintptr_t o_raise = (uintptr_t)raise - addr;
	uintptr_t o_dlopen = (uintptr_t)dlopen - addr;

	/*
	 * GET INFO ON TARGET
	 */
	pid = atoi(av[1]);

	uintptr_t addr_injectee_base = get_module_base(pid, "injectee");
	printf("injectee found at 0x%" PRIxPTR "\n", addr_injectee_base);

	uintptr_t addr_injectee_main = addr_injectee_base + 0x129d;
	printf("injectee!main at 0x%" PRIxPTR "\n", addr_injectee_main);

	uintptr_t addr_injectee_libc = get_module_base(pid, "libc");
	printf("injectee libc based at 0x%" PRIxPTR "\n", addr_injectee_libc);

	/*
	 * BUILD LOADER STUB
	 */
	uint32_t string_anchor;
	int stub_len = 0;
	uint8_t stub[1024];
	// mov rsi, 2 ; RTLD_NOW
	memcpy(stub + stub_len, "\x48\xc7\xc6\x02\x00\x00\x00", 7);
	stub_len += 7;
	// lea rax, rip + ???
	memcpy(stub + stub_len, "\x48\x8d\x05", 3);
	stub_len += 3;
	// ???
	memcpy(stub + stub_len, "\x90\x90\x90\x90", 4);
	stub_len += 4;
	string_anchor = stub_len;
	// mov rdi, rax
	memcpy(stub + stub_len, "\x48\x89\xc7", 3);
	stub_len += 3;
	// mov rax, ...
	memcpy(stub + stub_len, "\x48\xB8", 2);
	stub_len += 2;
	// address of dlopen() in injectee
	*(uintptr_t *)(stub + stub_len) = addr_injectee_libc + o_dlopen;
	stub_len += sizeof(uintptr_t);
	// call rax
	memcpy(stub + stub_len, "\xff\xd0", 2);
	stub_len += 2;
	// stop [and signal to debugger]
	if (1) {
		// breakpoint
		stub[stub_len] = '\xcc';
		stub_len += 1;
	}
	else {
		// self loop
		memcpy(stub + stub_len, "\xeb\xfe", 2);
		stub_len += 2;
	}
	// fixup the reference to the string, add string
	*(uint32_t *)(stub + string_anchor - 4) = stub_len - string_anchor;
	strcpy(stub + stub_len, "./injected.so");
	stub_len += strlen("./injected.so") + 1;
	// pad to 8 byte alignment
	while (stub_len % 8) {
		stub[stub_len] = '\x90';
		stub_len += 1;
	}
	printf("stub: ");
	for (int i=0; i<stub_len; ++i)
		printf("%02X", stub[i]);
	printf("\n");

	/*
	 * ATTACH, WRITE STUB, CONTINUE
	 */
	printf("attaching to process pid=%d\n", pid);
	rc = ptrace(PTRACE_ATTACH, pid, 0, 0);
	if (rc == -1) {
		perror("ptrace(PTRACE_ATTACH, ...)");
		exit(1);
	}

	// wait for SIG_STOP
	wait_debuggee(pid);

	/* write memory */
	iret = write_mem(pid, addr_injectee_main, stub, stub_len);
	if (iret != 0) {
		printf("ERROR: writing memory of injectee\n");
		exit(-1);
	}

	/* dump it back out */
	#define DUMPSZ 64
	uint8_t buf[DUMPSZ + sizeof(long)];
	rc = read_mem(pid, addr_injectee_main, DUMPSZ, buf);
	if (rc != 0) {
		exit(1);
	}
	hexdump(buf, DUMPSZ, addr_injectee_main);

	/* get regs */
	rc = ptrace(PTRACE_GETREGS, pid, NULL, &regs);
	if (rc == -1) {
		perror("ptrace(PTRACE_GETREGS, ...)");
		exit(1);
	}

	regs_old = regs;

	/* set regs (mainly pc/rip) */
	#ifdef __x86_64__
	regs.rip = addr_injectee_main;
	#endif
	#ifdef __arm__
	regs.pc = addr_injectee_main;
	#endif
	rc = ptrace(PTRACE_SETREGS, pid, NULL, &regs);
	if (rc == -1) {
		perror("ptrace(PTRACE_GETREGS, ...)");
		exit(1);
	}

	/* wait for breakpoint */
	ptrace(PTRACE_CONT, pid, 0, 0);
	wait_debuggee(pid);

	/* restore regs */
	ptrace(PTRACE_SETREGS, pid, NULL, &regs_old);

	printf("detaching from pid=%d\n", pid);
	lret = ptrace(PTRACE_DETACH, pid, 0, 0);
	if (lret == -1) {
		perror("ptrace(PTRACE_DETACH, ...)");
		exit(1);
	}

	return 0;
}
