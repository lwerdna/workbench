#!/usr/bin/env python

# generate the alphabet printing code with call/ret obfuscation

import random
alphabet = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ')
random.shuffle(alphabet)
for letter in alphabet:
    print('print_%c:' % letter)
    print('\tmov al, \'%c\'' % letter)
    print('\tcall output')
    if letter == 'Z':
        print('\tpush exit')
        #print('\tmov rax, exit')
    else:
        print('\tpush print_%c' % chr(ord(letter)+1))
        #print('\tmov rax, print_%c' % chr(ord(letter)+1))
    #print('\tpush rax')
    print('\tret')
    print('')
