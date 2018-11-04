In `int 0x80` legacy convention, system call number and parameters go easily into EAX,EBX,ECX,EDX.

In `syscall` convention, system call number is in EAX and then function parameters (RDI, RSI, RDX, RCX, R10, R8, R9) which, according to Wikipedia, deviates from System V X64 convention.

The syscall numbers changed between 32 and 64! On my Ubuntu 18.04 machine, 32-bit syscalls are in /usr/include/x86_64-linux-gnu/asm/unistd_32.h and the 64-bit ones are in unistd_64.h

All the programs work fine on my 64-bit Ubuntu machine, even the 32-bit ones using int 0x80 convention. It seems backwards compatibility is conveniently present. I had to `sudo apt-get install libc6-dev-i386`.
