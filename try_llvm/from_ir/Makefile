.PHONY: error

CLANG = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/clang
LD_LLD = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/ld.lld
LLD_LINK = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/lld-link
LD64 = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/ld64.lld
LLC = $(HOME)/Downloads/clang+llvm-13.0.0-x86_64-apple-darwin/bin/llc

TARGETS_ASM = hello-macos-x64.s hello-win-x64.s hello-win-x86.s hello-linux-x64.s hello-linux-x86.s hello-linux-arm.s
TARGETS_OBJ = hello-macos-x64.o hello-win-x64.o hello-win-x86.o hello-linux-x64.o hello-linux-x86.o hello-linux-arm.o
TARGETS_EXE = hello-macos-x64 hello-win-x64.exe hello-win-x86.exe hello-linux-x64 hello-linux-x86 hello-linux-arm

#all: $(TARGETS_ASM) $(TARGETS_OBJ) $(TARGETS_EXE)
all: $(TARGETS_ASM) $(TARGETS_OBJ)

interpret:
	lli hello.ll

hello.s: hello.ll
	llc hello.ll

hello: hello.ll
	clang hello.ll -o hello

#------------------------------------------------------------------------------
# assembler files
#------------------------------------------------------------------------------
hello-macos-x64.s: hello.ll
	$(LLC) -mtriple x86_64-apple-darwin hello.ll -o hello-macos-x64.s

hello-win-x64.s: hello.ll
	$(LLC) -mtriple x86_64-pc-win32 hello.ll -o hello-win-x64.s

hello-win-x86.s: hello.ll
	$(LLC) -mtriple i686-pc-win32 hello.ll -o hello-win-x86.s

hello-linux-x64.s: hello.ll
	$(LLC) -mtriple x86_64-none-linux-elf hello.ll -o hello-linux-x64.s

hello-linux-x86.s: hello.ll
	$(LLC) -mtriple i686-none-linux-elf hello.ll -o hello-linux-x86.s

hello-linux-arm.s: hello.ll
	$(LLC) -mtriple armv7-none-eabi hello.ll -o hello-linux-arm.s

#------------------------------------------------------------------------------
# object files
#------------------------------------------------------------------------------
hello-macos-x64.o: hello.ll
	$(LLC) -mtriple x86_64-apple-darwin hello.ll -filetype=obj -o hello-macos-x64.o

hello-win-x64.o: hello.ll
	$(LLC) -mtriple x86_64-pc-win32 hello.ll -filetype=obj -o hello-win-x64.o

hello-win-x86.o: hello.ll
	$(LLC) -mtriple i686-pc-win32 hello.ll -filetype=obj -o hello-win-x86.o

hello-linux-x64.o: hello.ll
	$(LLC) -mtriple x86_64-none-linux-elf hello.ll -filetype=obj -o hello-linux-x64.o

hello-linux-x86.o: hello.ll
	$(LLC) -mtriple i686-none-linux-elf hello.ll -filetype=obj -o hello-linux-x86.o

hello-linux-arm.o: hello.ll
	$(LLC) -mtriple armv7-none-eabi hello.ll -filetype=obj -o hello-linux-arm.o

#------------------------------------------------------------------------------
# executables
#------------------------------------------------------------------------------
hello-macos-x64: hello.o
	$(LLC) -mtriple=x86_64-apple-darwin hello.ll -filetype=macho -o hello-macos-x64

hello-win-x64.exe: hello.o
	$(LLC) -mtriple=x86_64-pc-win32 hello.ll -o hello-win-x64.exe

hello-win-x86.exe: hello.o
	$(LLC) -mtriple=i686-pc-win32 hello.ll -o hello-win-x86.exe

hello-linux-x64: hello.o
	$(LLC) -mtriple=x86_64-none-linux-elf hello.ll -o hello-linux-x64

hello-linux-x86: hello.o
	$(LLC) -mtriple=i686-none-linux-elf hello.ll -o hello-linux-x86

hello-linux-arm: hello.o
	$(LLC) -mtriple=armv7-none-eabi hello.ll -o hello-linux-arm


clean:
	rm -f $(TARGETS_ASM) $(TARGETS_OBJ) $(TARGETS_EXE)
