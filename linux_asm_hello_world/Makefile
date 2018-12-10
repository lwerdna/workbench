all: gas_x86_int80_att gas_x86_int80_intel gas_x64_syscall_att gas_x64_syscall_intel nasm_x86_int80

gas_x86_int80_att.o: gas_x86_int80_att.s
	as --32 ./gas_x86_int80_att.s -o gas_x86_int80_att.o
gas_x86_int80_att: gas_x86_int80_att.o
	ld -m elf_i386 gas_x86_int80_att.o -o gas_x86_int80_att

gas_x86_int80_intel.o: gas_x86_int80_intel.s
	as --32 ./gas_x86_int80_intel.s -o gas_x86_int80_intel.o
gas_x86_int80_intel: gas_x86_int80_intel.o
	ld -m elf_i386 gas_x86_int80_intel.o -o gas_x86_int80_intel

gas_x64_syscall_att.o: gas_x64_syscall_att.s
	as ./gas_x64_syscall_att.s -o gas_x64_syscall_att.o
gas_x64_syscall_att: gas_x64_syscall_att.o
	ld gas_x64_syscall_att.o -o gas_x64_syscall_att

gas_x64_syscall_intel.o: gas_x64_syscall_intel.s
	as ./gas_x64_syscall_intel.s -o gas_x64_syscall_intel.o
gas_x64_syscall_intel: gas_x64_syscall_intel.o
	ld gas_x64_syscall_intel.o -o gas_x64_syscall_intel

nasm_x86_int80.o: nasm_x86_int80.s
	nasm ./nasm_x86_int80.s -f elf32 -o nasm_x86_int80.o
nasm_x86_int80: nasm_x86_int80.o
	ld -m elf_i386 nasm_x86_int80.o -o nasm_x86_int80

clean:
	rm *.o gas_x86_int80_att gas_x86_int80_intel gas_x64_syscall_att gas_x64_syscall_intel nasm_x86_int80
