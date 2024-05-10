all: rlibc2

rlibc2: ret2libc2.o extra.o
	gcc ret2libc2.o extra.o -o rlibc2

ret2libc2.o: ret2libc2.c
	gcc -fno-stack-protector -c ret2libc2.c -o ret2libc2.o

extra.o: extra.s
	nasm extra.s -f elf64 -o extra.o

clean:
	rm -rf *.o rlibc rlibc2 rlibc-rop.txt peda-session-rlibc.txt peda-session-rlibc2.txt
