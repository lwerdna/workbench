PYTHON_CFLAGS = $(shell python2.7-config --cflags)
PYTHON_LDFLAGS = $(shell python2.7-config --ldflags)

all: call3

call3.o: call3.c a.py b.py c.py
	gcc -c call3.c -o call3.o $(PYTHON_CFLAGS)

call3: call3.o
	gcc call3.o -o call3 $(PYTHON_LDFLAGS)

capture_stdout.o: capture_stdout.c a.py b.py c.py
	gcc -c capture_stdout.c -o capture_stdout.o $(PYTHON_CFLAGS)

capture_stdout: capture_stdout.o
	gcc capture_stdout.o -o capture_stdout $(PYTHON_LDFLAGS)

clean:
	rm call3 *.o *.pyc
