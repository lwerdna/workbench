#!/usr/bin/env python3

import itertools

# Algorithm L from TAOCP Volume 4A, section 7.2.1.2
def generate(n):
    foo = list('('*(n//2) + ')'*(n//2))
    while 1:
        # L1
        print(''.join(foo))
        # L2
        j = len(foo)-2
        while foo[j] >= foo[j+1]:
            j -= 1
            if j == -1: return
        # L3
        l = len(foo)-1
        while foo[j] >= foo[l]:
            l -= 1
        (foo[j],foo[l]) = (foo[l],foo[j]) 
        # L4
        foo = foo[0:j+1] + list(reversed(foo[j+1:]))

# assume foo is list of '(' and ')'

# generate, then filter
def generate2(foo):
    def validate(foo):
        s = 0
        for e in foo:
            s += 1 if e=='(' else -1
            if s < 0: return False
        return True
        
    perms = filter(validate, itertools.permutations(foo))
    return list(set(perms))
       
def generate3(n, coords=(0,0), sol=''):
    if coords[0] < coords[1]:
        return []
    if coords[0] < n:
        generate3(n, (coords[0]+1, coords[1]), sol+'(')
    if coords[1] < n:
        generate3(n, (coords[0], coords[1]+1), sol+')')
    if coords == (n,n):
        print(sol)
        
    
#generate(10)
    
#print(validate(list('())(')))

#result = generate2(list('(((())))'))
#for r in result:
#    print(''.join(r))
#print('%d total' % len(result))

generate3(5)

