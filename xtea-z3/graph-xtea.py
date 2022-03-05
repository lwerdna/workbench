#!/usr/bin/env python

# make a graph of the xtea function with 

vindex = 0
def v(label):
    global vindex
    name = f'v{vindex}'
    vindex += 1

    palette_idx = 0
    shape = 'box'
    if 'xor' in label:
        palette_idx = 1
    elif 'key' in label:
        palette_idx = 2
        shape = 'ellipse'
    elif 'add' in label:
        palette_idx = 3
    elif 'shr' in label or 'shl' in label:
        palette_idx = 4

    print(f'{name}[label="{label}", fillcolor={palette_idx}, style=filled, shape={shape}];')
    return name

cindex = 0
def cluster():
    global cindex
    cindex += 1
    return f'cluster_{cindex}'

fround_to_key_idx = [
'dummy', 0, 3, 1, 2, 2, 1, 3, 0, 0, 0, 1, 3, 2, 2, 3, 1, 0, 0, 1, 0, 2, 3, 3, 2, 0, 1,
1, 1, 2, 0, 3, 3, 0, 2, 1, 1, 2, 1, 3, 0, 0, 3, 1, 2, 2, 1, 3, 1, 0, 0, 1, 3,
2, 2, 3, 2, 0, 1, 1, 0, 2, 3, 3, 2 ]
assert len(fround_to_key_idx) == 65

print('digraph G {')
#print('\trankdir=LR')
print('\tnode [colorscheme=pastel28];')

print('p0 [label="ptext[0]"]')
print('p0 -> a0;')
print('p1 [label="ptext[1]"]')
print('p1 -> b0;')

a, b = '', ''

for i in range(1):
    # incoming nodes already created
    a = f'a{i}'
    b = f'b{i}'

    fround = 2*i + 1
    shl4 = v('shl4')
    shr5 = v('shr5')
    xor = v('xor')
    add = v('add')
    xor2 = v('xor')
    key = v(f'key[{fround_to_key_idx[fround]}]')
    add2 = v('add')
    print(f'{b} -> {shl4}')
    print(f'{b} -> {shr5}')
    print(f'{b} -> {add}')
    print('subgraph %s {' % cluster())
    print('\tlabel = "feistel %d/64";' % (fround))
    print('\tstyle = filled;')
    print('\tcolor = lightgrey;')
    print(f'\t{shl4} -> {xor}')
    print(f'\t{shr5} -> {xor}')
    print(f'\t{xor} -> {add}')
    print(f'\t{add} -> {xor2}')
    print(f'\t{key} -> {xor2}')
    print(f'\t{xor2} -> {add2}')
    print('}')
    print(f'{a} -> {add2}')
    a = f'a{i+1}'
    print(f'{add2} -> {a}')

    fround = 2*i + 2
    shl4 = v('shl4')
    shr5 = v('shr5')
    xor = v('xor')
    add = v('add')
    xor2 = v('xor')
    key = v(f'key[{fround_to_key_idx[fround]}]')
    add2 = v('add')
    print(f'{a} -> {shl4}')
    print(f'{a} -> {shr5}')
    print(f'{a} -> {add}')
    print('subgraph %s {' % cluster())
    print('\trankdir=TB')
    print('\tlabel = "feistel %d/64";' % (fround))
    print('\tstyle = filled;')
    print('\tcolor = lightgrey;')
    print(f'\t{shl4} -> {xor}')
    print(f'\t{shr5} -> {xor}')
    print(f'\t{xor} -> {add}')
    print(f'\t{add} -> {xor2}')
    print(f'\t{key} -> {xor2}')
    print(f'\t{xor2} -> {add2}')
    print('}')
    print(f'{b} -> {add2}')
    b = f'b{i+1}'
    print(f'{add2} -> {b}')

print('c0 [label="ctext[0]"]')
print(f'{a} -> c0;')
print('c1 [label="ctext[1]"]')
print(f'{b} -> c1;')

print('}')
