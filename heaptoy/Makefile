FLAGS = -g -O0 -DUSE_DL_PREFIX -DMORECORE_CANNOT_TRIM

all: test gofer.so

test: test.c malloc.c malloc.h
	gcc $(FLAGS) test.c malloc.c -o test

gofer.so: gofer.c
	gcc $(FLAGS) gofer.c malloc.c -shared -o gofer.so

clean:
	rm -rf test
