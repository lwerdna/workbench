all: hello copy_to_phone

GDB = $(NDK)/bin/gdb
AS = $(NDK)/aarch64-linux-android/bin/as
LD = $(NDK)/aarch64-linux-android/bin/ld
OBJDUMP = $(NDK)/aarch64-linux-android/bin/objdump

hello: hello.o
	$(LD) -m aarch64elf hello.o -o hello

hello.o: hello.s
	 $(AS) hello.s -o hello.o

disasm:
	$(OBJDUMP) --disassemble-all ./hello

copy_to_phone: hello
	adb push ./hello /data/local/tmp

clean:
	rm -f hello hello.o
