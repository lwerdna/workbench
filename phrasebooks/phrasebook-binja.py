# target file and symbol
fpath = os.path.join(os.environ['HOME'], 'repos/lwerdna/workbench/testbins/tests-macos-x64-macho')
symbol = '_dream_cfg'
if sys.argv[2:]:
    fpath, symbol = sys.argv[1:3]
func = bv.get_functions_by_name(symbol)[0].llil.ssa_form

# OPEN FILE, GET FUNCTION BY NAME
import binaryninja
bview = binaryninja.open_view(fpath)
func = bview.get_functions_by_name(fname)[0]

# DISASSEMBLE SOME BYTES
data = b'\xc0\x03\x5f\xd6'
arch = binaryninja.Architecture['aarch64']
tokens, length = arch.get_instruction_text(data, 0) or ('', 0)
if length > 0:
    print(data.hex() + ': ' + ' '.join([t.text for t in tokens]))

# LIFT SOME BYTES
platform = binaryninja.Platform['linux-x86_64']
bview = binaryninja.binaryview.BinaryView.new(b'\x48\x0f\xc8') # bswap rax
bview.add_function(0, plat=platform)
print(bview.functions[0].low_level_il[0])

platform = binaryninja.Platform['linux-armv7']
bview = binaryninja.binaryview.BinaryView.new(b'\x32\x2f\xbf\xe6') # rev r2, r2
bview.add_function(0, plat=platform)
print(bview.functions[0].low_level_il[0])

# GENERATE GRAPH
print('digraph g {')
print('\t// nodes')
for block in func.low_level_il:
    label = f'bb{block.index} [{block.start},{block.end})'
    print(f'\t{block.index} [label="{label}"]')
print('\t// edges')
for src in func.low_level_il:
    for dst in src.dominator_tree_children:
        print(f'\t{src.index} -> {dst.index}')
print('}')

# PRINT LINEAR DISASSEMBLY OF FUNCTION
def bbtext(bb):
    return '\n'.join(['%08X: %s' % (l.address, l) for l in bb.get_disassembly_text()])

# print basic block
def print_basic_block_disasm(bb):
    lines = bbtext(bb).split('\n')

    for line in lines:
        m = re.match(r'^([a-hA-H0-9]{8,16}): (.*)$', line)
        if m:
            (addr, rest) = m.group(1,2)
            print('%s%s: %s%s' % (Style.DIM, addr, Style.RESET_ALL, rest))
            continue

        m = re.match(r'^b\d+:$', line)
        if m:
            continue

def print_function_disasm(func):
    basic_blocks = list(func.basic_blocks)
    for bb in sorted(basic_blocks, key=lambda bb: bb.start):
        print_basic_block_disasm(bb)

# find all instructions with 8 byte encoding
for f in bv.functions:
    for b in f:
        addr = b.start
        for toks, length in b:
            if length == 8:
                print(f'instruction {addr:08X}: {" ".join(t.text for t in toks)}')
            addr = addr + length
