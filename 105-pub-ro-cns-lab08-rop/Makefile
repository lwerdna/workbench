all: rlibc

rlibc: ret2libc.o extra.o
	gcc ret2libc.o extra.o -o rlibc

ret2libc.o: ret2libc.c
	gcc -fno-stack-protector -c ret2libc.c -o ret2libc.o

extra.o: extra.s
	nasm extra.s -f elf64 -o extra.o

clean:
	rm -rf *.o rlibc rlibc rlibc-rop.txt peda-session-rlibc.txt peda-session-rlibc.txt test-fds
