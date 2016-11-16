PYTHON_CFLAGS = $(shell python2.7-config --cflags)
PYTHON_LDFLAGS = $(shell python2.7-config --ldflags)

PYTHON_CFLAGS_EMB = -I ~/Downloads/Python-2.7.9/ \
				-I ~/Downloads/Python-2.7.9/Include
PYTHON_LDFLAGS_EMB = ~/Downloads/Python-2.7.9/libpython2.7.a

all: call3 capture_stdout full_embed

call3.o: call3.c a.py b.py c.py
	gcc -c call3.c -o call3.o $(PYTHON_CFLAGS)

call3: call3.o
	gcc call3.o -o call3 $(PYTHON_LDFLAGS)

capture_stdout.o: capture_stdout.c a.py b.py c.py
	gcc -c capture_stdout.c -o capture_stdout.o $(PYTHON_CFLAGS)

capture_stdout: capture_stdout.o
	gcc capture_stdout.o -o capture_stdout $(PYTHON_LDFLAGS)

full_embed.o: full_embed.c a.py b.py c.py
	gcc -c full_embed.c -o full_embed.o $(PYTHON_CFLAGS_EMB)

full_embed: full_embed.o
	gcc full_embed.o -o full_embed $(PYTHON_LDFLAGS_EMB)

clean:
	rm call3 *.o *.pyc
