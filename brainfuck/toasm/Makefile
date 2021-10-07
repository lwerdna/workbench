.PHONY: all

all: test

test.o: test.s
	nasm -f macho64 test.s -o test.o

test: test.o
	#ld -macosx_version_min 10.7.0 -lSystem test.o -o test
	ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem test.o -o test
