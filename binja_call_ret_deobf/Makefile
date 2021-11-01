.PHONY: all

all: obfuscated

obfuscated.o: obfuscated.s
	nasm -f macho32 obfuscated.s -o obfuscated.o

obfuscated: obfuscated.o
	ld -macosx_version_min 10.7.0 -lSystem obfuscated.o -o obfuscated
	#ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem obfuscated.o -o obfuscated	
