all: test

test: test.c libaaa.so libbbb.so
	gcc -O0 -m32 test.c -o test -L. -laaa -lbbb

libaaa.so: aaa.c
	gcc -O0 -m32 aaa.c -shared -fPIC -o libaaa.so

libbbb.so: bbb.c
	gcc -O0 -m32 bbb.c -shared -fPIC -o libbbb.so

relocs:
	readelf --relocs libaaa.so
	readelf --relocs libbbb.so

clean:
	rm -f test *.so *.out
