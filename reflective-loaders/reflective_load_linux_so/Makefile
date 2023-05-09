all: libfake.so libfake_so.h refload

libfake.so: libfake.c
	$(CC) -shared -fPIC libfake.c -o libfake.so

libfake_so.h: libfake.so
	xxd -i libfake.so > libfake_so.h

refload: refload.c libfake_so.h
	gcc refload.c -o refload -ldl -lrt

clean:
	rm -rf libfake.so libfake_so.h refload *.o *.so
