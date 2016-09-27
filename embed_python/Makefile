PYTHON_CFLAGS = $(shell python2.7-config --cflags)
PYTHON_LDFLAGS = $(shell python2.7-config --ldflags)

all: test

test.o: test.c a.py b.py c.py
	gcc -c test.c -o test.o $(PYTHON_CFLAGS)

test: test.o
	gcc test.o -o test $(PYTHON_LDFLAGS)

clean:
	rm test *.o *.pyc
