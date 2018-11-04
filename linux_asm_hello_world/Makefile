all: hello32_int80_att hello32_int80_intel hello64_syscall_intel

hello32_int80_att.o: hello32_int80_att.s
	as --32 ./hello32_int80_att.s -o hello32_int80_att.o

hello32_int80_att: hello32_int80_att.o
	ld -m elf_i386 hello32_int80_att.o -o hello32_int80_att

hello32_int80_intel.o: hello32_int80_intel.s
	as --32 ./hello32_int80_intel.s -o hello32_int80_intel.o

hello32_int80_intel: hello32_int80_intel.o
	ld -m elf_i386 hello32_int80_intel.o -o hello32_int80_intel

hello64_syscall_intel.o: hello64_syscall_intel.s
	as ./hello64_syscall_intel.s -o hello64_syscall_intel.o

hello64_syscall_intel: hello64_syscall_intel.o
	ld hello64_syscall_intel.o -o hello64_syscall_intel

clean:
	rm *.o hello32_int80_att hello32_int80_intel hello64_syscall_intel
