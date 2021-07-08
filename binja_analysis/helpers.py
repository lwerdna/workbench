import binaryninja
from binaryninja import core
from binaryninja import binaryview

from colorama import Fore, Back, Style

def bytes_to_function(data, plat_name='linux-x86_64'):
	bv = binaryview.BinaryView.new(data)

	platform = binaryninja.Platform[plat_name]
	bv.platform = platform
	bv.add_function(0, plat=platform)
	bv.update_analysis_and_wait()

	print_binary_view(bv)
	assert len(bv.functions) == 1
	return bv.functions[0]

def print_basic_block_disasm(bb):
	disassembly_text_lines = bb.get_disassembly_text()
	print(Fore.GREEN, '; %s has %d instructions' % \
	  (str(bb), len(disassembly_text_lines)), Style.RESET_ALL)
	for disassembly_text_line in disassembly_text_lines:
		print(Style.DIM, '%08X:' % disassembly_text_line.address, Style.RESET_ALL, end='')
		print('%s' % (str(disassembly_text_line)))

def print_function_disasm(func):
	print(Fore.GREEN, '; %s has %d basic blocks' % (str(func), len(func.basic_blocks)), Style.RESET_ALL)
	for bb in sorted(func.basic_blocks, key=lambda bb: bb.start):
		print_basic_block_disasm(bb)

# binaryview has functions
# functions have basicblocks
def print_binary_view(bv):
	for func in bv.functions:
		print_function_disasm(func)

