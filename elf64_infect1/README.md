elf64 infection method: for the usual case where there's both a virtual mem
gap and a file gap between the end of the code segment and the start of the
data segment, code can be located here by just expanding the length of the
code segment via the header

this appended code is right after the section ".eh_frame" in my experiments

before:
```
  Type           Offset             VirtAddr           PhysAddr
                 FileSiz            MemSiz              Flags  Align
  LOAD           0x0000000000000000 0x0000000000400000 0x0000000000400000
                 0x000000000000070c 0x000000000000070c  R E    200000
  LOAD           0x0000000000000e10 0x0000000000600e10 0x0000000000600e10
                 0x0000000000000230 0x0000000000000238  RW     200000
```

after:
```
  Type           Offset             VirtAddr           PhysAddr
                 FileSiz            MemSiz              Flags  Align
  LOAD           0x0000000000000000 0x0000000000400000 0x0000000000400000
                 0x0000000000000714 0x0000000000000714  R E    200000
  LOAD           0x0000000000000e10 0x0000000000600e10 0x0000000000600e10
                 0x0000000000000230 0x0000000000000238  RW     200000
```

# dynamic loader notes
* in Linux, Android, and FreeBSD at least, the OS loads the ELF to memory along with the dynamic loader object specified in the .interp section
* this loader is given control and contains most of the pecularities of how your ELF actually runs
* for example, there may be referenced shared object routines, init/fini functions, TLS variable initializers, and even consideration of environment variables for loggering or other loader variable behavior
## Android dynamic loader
* more to come, look in the bionic repo
## FreeBSD dynamic loader
* `cd /usr/src/libexec/rtld-elf`
* see in rtld.c function _rtld()
* compile for debug with `make DEBUG_FLAGS=-g DEBUG=-DDEBUG MK_TESTS=no all`
* replace current loader with `sudo chflags noschg /libexec/ld-elf.so.1` and then backup or snapshot VM and `mv` on top of it
* enable loader output to stderr with LD_DEBUG environment variable, eg: `LD_DEBUG=1 myelf`
* thanks to curoos on freenode for help


