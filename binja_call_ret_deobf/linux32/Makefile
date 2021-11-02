.PHONY: all

all: obfuscated

obfuscated.s: header.s footer.s ../generate.py
	cat header.s > obfuscated.s
	../generate.py 32 >> obfuscated.s
	cat footer.s >> obfuscated.s

obfuscated.o: obfuscated.s
	nasm -f elf32 obfuscated.s -o obfuscated.o

obfuscated: obfuscated.o
	ld -m elf_i386 obfuscated.o -o obfuscated

clean:
	rm -f *.o obfuscated.s
