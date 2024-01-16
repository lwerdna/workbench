import re

README = '''
# for "ripping" functions
# intended method of use:
# from binaryninja python console add this path to the import path
sys.path.append(os.path.join(os.environ['HOME'], 'repos/lwerdna/workbench/binja-sandbox'))
from importlib import reload
import rip
reload(rip) and rip.thumb(bv, current_function)

rip.nasm(bv, current_function)
'''

def thumb(bv, func):
    bxx = ['b', 'beq', 'bne', 'bs', 'bcc', 'bmi', 'bpl', 'bvs', 'bvc', 'bhi', 'bls',
            'bge', 'blt', 'bgt', 'ble', 'bal', 'bne']

    print('.thumb')
    print('.syntax unified')
    print('')
    print('.text')
    print('')
    print('.global _start')
    print('')
    print(f'.thumb_func')
    print(f'{func.name}:')

    callees = set()
    datees = set()

    first_block = True
    for bblock in sorted(func.basic_blocks, key=lambda bb: bb.start):
        addr = bblock.start

        if not first_block:
            print(f'loc_{addr:x}:')
        first_block = False

        for tokens, length in bblock:
            tokens = [t.text for t in tokens]
            mnemonic = tokens[0]

            # special handle calls
            if mnemonic == 'bl':
                assert tokens[1].isspace()
                if tokens[2] == '#': # skip hashmark if it preceeds function names
                    del tokens[2]
                if re.match(r'^0x[0-9a-fA-F]+$', tokens[2]):
                    tokens[2] = bv.get_function_at(int(tokens[2], 16)).name
                callees.add(tokens[2])
            # special handle branches
            elif mnemonic in bxx:
                if tokens[2] == '#': # skip hashmark if it preceeds destination
                    del tokens[2]
                if re.match(r'^0x[0-9a-fA-F]+$', tokens[2]):
                    tokens[2] = 'loc_'+tokens[2][2:]
            # all other instructions
            else:
                pass

            instxt = ''.join(tokens)
            print('\t' + instxt)
            addr += length

    print('')

    # collected function stub
    for f in callees:
        print('')
        print(f + ':')
        print('\tb\tlr')

    print('')
    print('.data')
    print('')
    for addr in datees:
        print(f'data_{addr:x}:')
        sample = bv.read(addr, 64)
        print('\tdb ', ', '.join(hex(b) for b in sample))

    print('')

    print('stuff:')
    print('dd		0, 1, 2, 3, 4, 5, 6, 7')
    print('dd		8, 9, 10, 11, 12, 13, 14, 15')

def nasm(bv, func):
    jxx = ['jo', 'jno', 'js', 'jns', 'je', 'jz', 'jne', 'jnz', 'jb', 'jnae', 'jc', 'jnb',
            'jae', 'jnc', 'jbe', 'jna', 'ja', 'jnbe', 'jl', 'jnge', 'jge', 'jnl'
            'jle', 'jng', 'jg', 'jnle', 'jp', 'jpe', 'jnp', 'jpo', 'jcxz', 'jecxz', 'jmp']

    print('BITS 64')
    print('default rel')
    print('')
    print('global _main')
    print('')
    print('section .text')
    print('')
    print('_main:')
    print('    retn')
    print('')
    print(f'{func.name}:')

    callees = set()
    datees = set()

    first_block = True
    for bblock in sorted(func.basic_blocks, key=lambda bb: bb.start):
        addr = bblock.start

        if not first_block:
            print(f'.loc_{addr:x}:')
        first_block = False

        for tokens, length in bblock:
            text_toks = [t.text for t in tokens]
            mnemonic = text_toks[0]

            # modify
            #print(f'    toks: {text_toks}')
            for i in range(len(text_toks)):
                #if text_toks[i] == 'rel ':
                #    print(f'    toks: {text_toks}')

                if re.match(r'^0x[0-9a-fA-F]+$', text_toks[i]):
                    addr = int(text_toks[i], 16)
                    if mnemonic == 'call':
                        func = bv.get_function_at(addr)
                        text_toks[i] = func.name
                        callees.add(func.name)
                    elif mnemonic in jxx:
                        text_toks[i] = '.loc_'+text_toks[i][2:]
                elif text_toks[i] in ['xmmword', 'xmmword ']:
                    text_toks[i] = ''
                elif mnemonic == 'nop' and i != 0: # nop's with operands become plain nop's
                    text_toks[i] = ''
                elif i == len(text_toks)-4:
                    if text_toks[i]=='[' and (text_toks[i+1] in ['rel', 'rel ']) and text_toks[i+3]==']':
                        if re.match(r'^0x[0-9a-fA-F]+$', text_toks[i+2]):
                            addr = int(text_toks[i+2], 16)
                            text_toks[i] = text_toks[i+1] = text_toks[i+3] = ''
                            text_toks[i+2] = 'data_'+hex(addr)[2:]
                            datees.add(addr)
                            break

            instxt = ''.join(text_toks)
            print('\t' + instxt)
            addr += length

    print('')

    # collected function stub
    for f in callees:
        print('')
        print(f + ':')
        print('\tretn')

    print('')
    print('section .data')
    print('')
    for addr in datees:
        print(f'data_{addr:x}:')
        sample = bv.read(addr, 64)
        print('\tdb ', ', '.join(hex(b) for b in sample))

    print('')

    print('stuff:')
    print('dd		0, 1, 2, 3, 4, 5, 6, 7')
    print('dd		8, 9, 10, 11, 12, 13, 14, 15')

