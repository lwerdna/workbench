TOOLS = $(HOME)/android_a64_api21_toolchain/bin/arm-linux-androideabi

all: using-ldr using-tbb

using-ldr: using-ldr.o
	$(TOOLS)-ld using-ldr.o -o using-ldr --entry SetSemaphore

using-ldr.o: using-ldr.s
	$(TOOLS)-as -mthumb using-ldr.s -o using-ldr.o
	$(TOOLS)-strip --discard-all --verbose using-ldr.o -o using-ldr.o

using-tbb: using-tbb.o
	$(TOOLS)-ld using-tbb.o -o using-tbb --entry SetSemaphore

using-tbb.o: using-tbb.s
	$(TOOLS)-as -mthumb using-tbb.s -o using-tbb.o
	$(TOOLS)-strip --discard-all --verbose using-tbb.o -o using-tbb.o

clean:
	rm -rf *.o using-ldr using-tbb
