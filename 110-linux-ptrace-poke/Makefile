all: tracer tracee tracer-arm

tracer: tracer.c
	gcc tracer.c -o tracer

tracer-arm: tracer.c
	arm-linux-gnueabi-gcc -static tracer.c -o tracer-arm

tracee: tracee.c
	gcc tracee.c -o tracee

clean:
	rm -f tracer tracer-arm tracee
