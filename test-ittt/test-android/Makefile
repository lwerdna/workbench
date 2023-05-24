all: hello

NDK = $(HOME)/android-ndk-r21d-built
NDK_BIN_PATH = $(NDK)/bin/arm-linux-androideabi-
AS = $(NDK_BIN_PATH)as
LD = $(NDK_BIN_PATH)ld
OBJDUMP = $(NDK_BIN_PATH)objdump

hello: hello.o
	# see `ld -V` for other -m options
	$(LD) hello.o -o hello

hello.o: hello.s
	 $(AS) -mthumb hello.s -o hello.o

disasm:
	$(OBJDUMP) -d hello.o

clean:
	rm -f hello hello.o a.out
