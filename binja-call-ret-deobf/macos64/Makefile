.PHONY: all

all: obfuscated

obfuscated.s: header.s footer.s ../generate.py
	cat header.s > obfuscated.s
	../generate.py 64 >> obfuscated.s
	cat footer.s >> obfuscated.s

obfuscated.o: obfuscated.s
	nasm -f macho64 obfuscated.s -o obfuscated.o

obfuscated: obfuscated.o
	#ld -macosx_version_min 10.7.0 -lSystem obfuscated.o -o obfuscated
	ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem obfuscated.o -o obfuscated	
