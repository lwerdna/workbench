# deobfuscate "push <uint32_t>; ret;"
#
# this is intended to be loaded from the binja console
#
# >>> sys.path.append('/path/to/this/script')
# >>> import deobfuscate
# >>> deobfuscate.deobfuscate_all(bv)
#
# you can edit/reload with:
#
# >>> import importlib
# >>> importlib.reload(deobfuscate)

def deobfuscate_function(bv, func):
    for block in func.basic_blocks:
        (instrs, lengths) = zip(*[i for i in block])
        addrs = [block.start + sum(lengths[0:i]) for i in range(len(lengths))]

        for i in range(len(instrs)-1):
            if instrs[i][0].text == 'push' and (instrs[i+1][0].text in ['ret', 'retn']):
                source = 'jmp '+instrs[i][-1].text
                data = bv.arch.assemble(source, addrs[i])
                while len(data) < lengths[i]+lengths[i+1]:
                    data += b'\x90'
                print('%08X: push+ret found, assembled %s to %s, patching...' % (addrs[i], source, data))
                bv.write(addrs[i], data)

def deobfuscate_all(bv):
    for func in bv.functions:
        deobfuscate_function(bv, func)
