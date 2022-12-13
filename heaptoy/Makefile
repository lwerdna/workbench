FLAGS = -g -O0 -DUSE_DL_PREFIX -DMORECORE_CANNOT_TRIM

all: test

test: test.c malloc.c malloc.h
	gcc $(FLAGS) test.c malloc.c -o test

clean:
	rm -rf test
