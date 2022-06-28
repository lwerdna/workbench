all: out0.o out1.o

out0.o: example_2_1.asm
	nasm -f elf64 example_2_1.asm -o out0.o

out1.o: example_2_1.c
	gcc -c example_2_1.c -o out1.o
	
example_2_1.asm: example_2_1.py py2asm.py
	./py2asm.py example_2_1.py > example_2_1.asm

example_2_1.c: example_2_1.py py2c.py
	./py2c.py example_2_1.py > example_2_1.c

clean:
	rm -rf example_2_1.asm example_2_1.c *.o *.so __pycache__
