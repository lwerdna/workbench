all: tests-macos-x64-macho

lowlevel.o: lowlevel.asm
	nasm -f macho64 lowlevel.asm -o lowlevel.o
	# -x removes all local syms (keeps global)
	strip -x ./lowlevel.o
	#strip -s ./keep-syms.txt ./lowlevel.o

tests.o: tests.c
	gcc -g -O0 -c tests.c -o tests.o

tests-macos-x64-macho: tests.o lowlevel.o
	gcc -g -O0 tests.o lowlevel.o -o tests-macos-x64-macho
	./rm-func-starts.py ./tests-macos-x64-macho

clean:
	rm -f tests-macos-x64-macho lowlevel.o tests.o
