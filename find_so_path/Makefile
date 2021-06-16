test: test.o libso.so
	gcc test.o -o $@ -Wl,-L.,-lso,-rpath,'$$ORIGIN'

clean:
	rm -f libso.so test.o test

libso.so: so.c
	gcc -D_GNU_SOURCE=1 -fPIC -shared $< -o $@ -lc -ldl

test.o: test.c
	gcc -fPIC -c $< -o $@
