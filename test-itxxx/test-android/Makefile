all: demo-eq demo-lt

NDK = $(HOME)/android-ndk-r21d-built
NDK_BIN_PATH = $(NDK)/bin/arm-linux-androideabi-
AS = $(NDK_BIN_PATH)as
LD = $(NDK_BIN_PATH)ld
OBJDUMP = $(NDK_BIN_PATH)objdump

demo-eq: demo-eq.o
	# see `ld -V` for other -m options
	$(LD) demo-eq.o -o demo-eq

demo-eq.o: demo-eq.s
	 $(AS) -mthumb demo-eq.s -o demo-eq.o

demo-lt: demo-lt.o
	$(LD) demo-lt.o -o demo-lt

demo-lt.o: demo-lt.s
	 $(AS) -mthumb demo-lt.s -o demo-lt.o

disasm:
	$(OBJDUMP) -d demo-eq.o
	$(OBJDUMP) -d demo-lt.o

clean:
	rm -f demo-eq demo-eq.o a.out
	rm -f demo-lt demo-lt.o a.out
