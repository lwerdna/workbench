all: injector injectee injected.so

injector: injector.c
	gcc -g injector.c -o injector

injector-arm: injector.c
	arm-linux-gnueabi-gcc -static injector.c -o injector-arm

injectee: injectee.c
	gcc -g injectee.c -o injectee -ldl

injected.so: injected.c
	gcc injected.c -shared -o injected.so

clean:
	rm -f injector injector-arm injectee injected.so
