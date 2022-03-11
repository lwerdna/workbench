#!/usr/bin/env python

# generate alphabet printing code with call/ret obfuscation
#
# 32 bit version:
#    push foo
#    ret
#
# 64-bit version:
#    mov rax, foo
#    push rax
#    ret

import random, sys
alphabet = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
random.shuffle(alphabet)
for letter in alphabet:
    print('print_%c:' % letter)
    print('\tmov al, \'%c\'' % letter)
    print('\tcall output')
    if letter == 'Z':
        if sys.argv[1]=='32':
            print('\tpush exit')
        elif sys.argv[1]=='64':
            print('\tmov rax, exit')
    else:
        if sys.argv[1]=='32':
            print('\tpush print_%c' % chr(ord(letter)+1))
        elif sys.argv[1]=='64':
            print('\tmov rax, print_%c' % chr(ord(letter)+1))

    if sys.argv[1]=='64':
        print('\tpush rax')
    print('\tret')
    print('')
