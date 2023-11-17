def README():
    # for "ripping" functions
    # intended method of use:
    # from binaryninja python console add this path to the import path
     sys.path.append(os.path.join(os.environ['HOME'], 'repos/lwerdna/workbench/binja-sandbox'))
     import rip
     rip.nasm(current_function)

    # when developing this is useful:
     from importlib import reload
     reload(rip)

def nasm(bv, func):
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
    for bblock in sorted(func.basic_blocks, key=lambda bb: bb.start):
        addr = bblock.start
        for tokens, length in bblock:
            data = bv.read(addr, length)
            instxt = ''.join(t.text for t in tokens)
            print('\t' + instxt)
            addr += length

    print('')
    print('section .data')
    print('')
    print('stuff:')
    print('dd		0, 1, 2, 3, 4, 5, 6, 7')
    print('dd		8, 9, 10, 11, 12, 13, 14, 15')

