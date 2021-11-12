.PHONY: all clean

CLANG = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/clang
LD_LLD = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/ld.lld
LLD_LINK = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/lld-link
LD64 = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/ld64.lld

all: foo-linux-x86.so foo-linux-x64.so foo-linux-arm.so foo-win-x86.dll foo-win-x64.dll foo-macos-x64.dylib

foo-macos-x64.dylib: foo-macos-x64.o
	$(LD64) -arch x86_64 -platform_version "macos" "11.0.0" "11.0" -dylib foo-macos-x64.o -o foo-macos-x64.dylib

foo-macos-x64.o: foo.c
	$(CLANG) -fpic -target x86_64-apple-darwin -c foo.c -o foo-macos-x64.o

foo-win-x64.dll: foo-win-x64.o
	$(LLD_LINK) foo-win-x64.o /dll /subsystem:console /nodefaultlib /noentry /out:foo-win-x64.dll

foo-win-x64.o: foo.c
	$(CLANG) -target x86_64-pc-win32 -c foo.c -o foo-win-x64.o

foo-win-x86.dll: foo-win-x86.o
	$(LLD_LINK) foo-win-x86.o /dll /subsystem:console /nodefaultlib /noentry /out:foo-win-x86.dll

foo-win-x86.o: foo.c
	$(CLANG) -target i686-pc-win32 -c foo.c -o foo-win-x86.o

foo-linux-x64.so: foo-linux-x64.o
	#$(LD_LLD) -o foo-linux-x64.so --dynamic-linker=/lib64/ld-linux-x86-64.so.2 foo-linux-x64.o
	$(LD_LLD) --shared foo-linux-x64.o -o foo-linux-x64.so

foo-linux-x64.o: foo.c
	$(CLANG) -fpic -target x86_64-none-linux-elf -c foo.c -o foo-linux-x64.o

foo-linux-x86.so: foo-linux-x86.o
	$(LD_LLD) --shared foo-linux-x86.o -o foo-linux-x86.so

foo-linux-x86.o: foo.c
	$(CLANG) -fpic -target i686-none-linux-elf -c foo.c -o foo-linux-x86.o

foo-linux-arm.so: foo-linux-arm.o
	$(LD_LLD) --shared foo-linux-arm.o -o foo-linux-arm.so

foo-linux-arm.o: foo.c
	$(CLANG) -fpic -target armv7-none-eabi -c foo.c -o foo-linux-arm.o

clean:
	rm -f \
	foo-linux-x64.o foo-linux-x64.so \
	foo-linux-arm.o foo-linux-arm.so \
	foo-linux-x86.o foo-linux-x86.so \
	foo-win-x86.o foo-win-x86.lib foo-win-x86.dll \
	foo-win-x64.o foo-win-x64.lib foo-win-x64.dll \
	foo-macos-x64.o foo-macos-x64.dylib
