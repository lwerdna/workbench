#!/bin/bash
llvm-mc-mp-3.7 -assemble -arch=x86 x86.s -o x86.o -filetype=obj
llvm-mc-mp-3.7 -assemble -arch=x86-64 x86-64.s -o x86-64.o -filetype=obj
llvm-mc-mp-3.7 -assemble -arch=arm arm.s -o arm.o -filetype=obj
llvm-mc-mp-3.7 -assemble -arch=arm64 arm64.s -o arm64.o -filetype=obj
llvm-mc-mp-3.7 -assemble -arch=thumb thumb.s -o thumb.o -filetype=obj
llvm-mc-mp-3.7 -assemble -arch=ppc32 ppc32.s -o ppc32.o -filetype=obj
llvm-mc-mp-3.7 -assemble -arch=ppc64 ppc64.s -o ppc64.o -filetype=obj

