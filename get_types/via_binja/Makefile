test: test.c libtest.so
	gcc test.c -o test -L. -ltest

libtest.so: libtest.c
	gcc -shared libtest.c -o libtest.so
