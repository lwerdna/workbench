all: injector injectee injector-arm injected.so

injector: injector.c
	gcc -g injector.c -o injector

injector-arm: injector.c
	arm-linux-gnueabi-gcc -static injector.c -o injector-arm

injectee: injectee.c
	gcc injectee.c -o injectee

injected.so: injected.c
	gcc injected.c -shared -o injected.so

clean:
	rm -f injector injector-arm injectee injected.so
