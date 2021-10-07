#!/usr/bin/env python

# translate brainfuck to x64
# + trivial intermediate language
# + trivial optimizations 

import os, sys, re, pprint

print('; brainfuck assembly translation of %s\n' % sys.argv[1])

with open('prologue.s') as fp:
    print(fp.read())

# convert bf commands to IL
def to_il(c):
    if c == '>': return {'op':'right', 'repeat':1}
    if c == '<': return {'op':'left', 'repeat':1}
    if c == '+': return {'op':'inc', 'repeat':1}
    if c == '-': return {'op':'dec', 'repeat':1}
    if c == '.': return {'op':'out', 'repeat':1}
    if c == ',': return {'op':'in', 'repeat':1}
    if c == '[': return {'op':'loop_start', 'repeat':1}
    if c == ']': return {'op':'loop_end', 'repeat':1}
    return {'op':'nop', 'repeat':1}

def remove_nops(code):
    return [il for il in code if il['op'] != 'nop']

def collapse(code):
    result = []
    i = 0;
    while i<len(code):
        n = 1
        if not code[i]['op'] in ['loop_start', 'loop_end', 'out', 'in']:
            while (i+n)<len(code)-1 and code[i]['op'] == code[i+n]['op']:
                n += 1
        result.append({'op':code[i]['op'], 'repeat':n})
        i += n
    return result 

def collapse_recursive(code):
    if len(code)<=1:
        return code

    (x, xs) = (code[0], code[1:])
    subresult = collapse(xs)

    if x['op'] == subresult[0]['op']:
        subresult[0]['repeat'] += 1
        return subresult
    else:
        return [x] + subresult

def print_il(code):
    for (i,il) in enumerate(code):
        print('%s.%d' % (il['op'], il['repeat']))

# code from file
with open(sys.argv[1]) as fp:
    code = fp.read()
# code to IL
code = [to_il(c) for c in code]
code = remove_nops(code)
code = collapse(code)

# validate matching []'s
jmp = {}
stack = []
for (i,il) in enumerate(code):
    if il['op'] == 'loop_start':
        stack.append(i)
    elif il['op'] == 'loop_end':
        jmp[stack[-1]] = i
        jmp[i] = stack.pop()

#
for (i,il) in enumerate(code):
    (op, repeat) = (il['op'], il['repeat'])
    if op == 'right':
        if repeat==1:
            print('\tinc rdi')
        else:
            print('\tadd rdi, %d' % repeat)
    elif op == 'left':
        if repeat==1:
            print('\tdec rdi')
        else:
            print('\tsub rdi, %d' % repeat)
    elif op == 'inc':
        if repeat==1:
            print('\tinc byte [rdi]')
        else:
            print('\tadd byte [rdi], %d' % repeat)
    elif op == 'dec':
        if repeat==1:
            print('\tdec byte [rdi]')
        else:
            print('\tsub byte [rdi], %d' % repeat)
    elif op == 'out':
        print('\tcall output')
    elif op == 'in':
        print('\tcall input')
    elif op == 'loop_start':
        print('\tcmp byte [rdi], 0')
        print('\tjz loc_%d' % jmp[i]) 
        print('loc_%d:' % i)
    elif op == 'loop_end':
        print('\tcmp byte [rdi], 0')
        print('\tjnz loc_%d' % jmp[i])     
        print('loc_%d:' % i)
    else:
        # ...possibly interspersed with other characters (which are ignored)
        pass

with open('epilogue.s') as fp:
    print(fp.read())
