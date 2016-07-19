#!/bin/bash
# generate .s files
# clang -S -emit-llvm will produce hello.ll (llvm IR)
# clang -S -c will produce .s (assembler) but it's difficult to specify target
# llc will produce hello.s

# must target at compile time, resulting .s has target triple specified and
# cpu-specific flags
clang -S -c -target i686-pc-none hello.c -o x86.s
clang -S -c -target x86_64-pc-none hello.c -o x86_64.s
clang -S -c -target arm-pc-none hello.c -o arm.s
clang -S -c -target arm64-pc-none hello.c -o arm64.s
clang -S -c -arch ppc hello.c -o ppc.s
clang -S -c -target mips-pc-none hello.c -o mips.s

llvm-mc-mp-3.7 -assemble x86.s -o x86.o -filetype=obj
llvm-mc-mp-3.7 -assemble x86_64.s -o x86-64.o -filetype=obj
llvm-mc-mp-3.7 -assemble arm.s -o arm.o -filetype=obj
llvm-mc-mp-3.7 -assemble arm64.s -o arm64.o -filetype=obj
#llvm-mc-mp-3.7 -assemble thumb.s -o thumb.o -filetype=obj
llvm-mc-mp-3.7 -assemble ppc.s -o ppc.o -filetype=obj
llvm-mc-mp-3.7 -assemble mips.s -o ppc.o -filetype=obj

