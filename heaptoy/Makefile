FLAGS = -g -O0 -DUSE_DL_PREFIX

all: toy

toy: main.c malloc.c malloc.h
	gcc $(FLAGS) main.c malloc.c -o toy

clean:
	rm -rf toy
