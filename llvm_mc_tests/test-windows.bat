rem release from (for example) http://llvm.org/releases/3.6.2/LLVM-3.6.2-win32.exe
rem do not contain llvm-mc, used instead: https://github.com/CRogers/LLVM-Windows-Binaries
rem
c:\llvm-3.4-tools-windows\llvm-mc.exe -assemble -arch=x86 x86.s -o x86.o -filetype=obj
c:\llvm-3.4-tools-windows\llvm-mc.exe -assemble -arch=x86-64 x86-64.s -o x86-64.o -filetype=obj
c:\llvm-3.4-tools-windows\llvm-mc.exe -assemble -arch=arm arm.s -o arm.o -filetype=obj
c:\llvm-3.4-tools-windows\llvm-mc.exe -assemble -arch=arm64 arm64.s -o arm64.o -filetype=obj
c:\llvm-3.4-tools-windows\llvm-mc.exe -assemble -arch=thumb thumb.s -o thumb.o -filetype=obj
c:\llvm-3.4-tools-windows\llvm-mc.exe -assemble -arch=ppc32 ppc32.s -o ppc32.o -filetype=obj
c:\llvm-3.4-tools-windows\llvm-mc.exe -assemble -arch=ppc64 ppc64.s -o ppc64.o -filetype=obj

