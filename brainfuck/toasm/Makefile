.PHONY: all

all: helloworld 99bob add_2_5

helloworld.s: translate.py ../helloworld.bf
	./translate.py ../helloworld.bf > helloworld.s

helloworld.o: helloworld.s
	nasm -f macho64 helloworld.s -o helloworld.o

helloworld: helloworld.o
	#ld -macosx_version_min 10.7.0 -lSystem helloworld.o -o helloworld
	ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem helloworld.o -o helloworld

99bob.s: translate.py ../99bob.bf
	./translate.py ../99bob.bf > 99bob.s

99bob.o: 99bob.s
	nasm -f macho64 99bob.s -o 99bob.o

99bob: 99bob.o
	#ld -macosx_version_min 10.7.0 -lSystem 99bob.o -o 99bob
	ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem 99bob.o -o 99bob

add_2_5.s: translate.py ../add_2_5.bf
	./translate.py ../add_2_5.bf > add_2_5.s

add_2_5.o: add_2_5.s
	nasm -f macho64 add_2_5.s -o add_2_5.o

add_2_5: add_2_5.o
	#ld -macosx_version_min 10.7.0 -lSystem add_2_5.o -o add_2_5
	ld -L /Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem add_2_5.o -o add_2_5	
