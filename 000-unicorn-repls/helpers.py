import re
import struct

from termcolor import colored

from unicorn.arm_const import *
from unicorn.unicorn_const import *

def align_down_4k(addr):
    return addr & 0xFFFFFFFFFFFFF000 # lose the bottom 12 bits (4k)

def align_up_4k(addr):
    return align_down_4k(addr) + 0x1000 if (addr & 0xFFF) else addr

def align_4k(addr):
    return (align_down_4k(addr), align_up_4k(addr+1))

def map_needed_pages(uc, addr, size, perms):
    lo = align_down_4k(addr)
    hi = align_up_4k(addr+size)
    print(f'uc.mem_map(0x{lo:X}, 0x{hi-lo:X}) -> [0x{lo:X}, 0x{hi:X})')
    uc.mem_map(lo, hi-lo, perms=perms)

def get_hex_dump(data, addr=0, grouping=1, endian='little'):
	result = ''
	while(data):
		ascii = ''
		buff16 = data[0:16]
		data = data[16:]
		result += "%08X: " % addr
		i = 0
		while i < 16:
			if(i < len(buff16)):
				f0 = { \
					'big':	{1:'>B', 2:'>H', 4:'>I', 8:'>Q'}, \
					'little': {1:'<B', 2:'<H', 4:'<I', 8:'<Q'} \
				}
				f1 = { \
					1:'%02X ', 2:'%04X ', 4:'%08X ', 8:'%016X ' \
				}
				temp = struct.unpack(f0[endian][grouping], buff16[i:i+grouping])[0]
				result += f1[grouping] % temp
				for j in range(grouping):
					if(buff16[i+j] >= ord(' ') and buff16[i+j] <= ord('~')):
						ascii += chr(buff16[i+j])
					else:
						ascii += '.'
			else:
				if grouping == 1:
					result += ' '*len('DE ')
				elif grouping == 2:
					result += ' '*len('DEAD ')
				elif grouping == 4:
					result += ' '*len('DEADBEEF ')
				elif grouping == 8:
					result += ' '*len('DEADBEEFCAFEBABE ')
			i += grouping
		result += ' %s\n' % ascii
		addr += 16;
	return result

def parse_bytes_permissive(string):
    nybles = ''.join([c for c in string if c != ' '])
    if len(nybles) % 2: nybles = '0'+nybles
    bytes_ = [nybles[i:i+2] for i in range(0, len(nybles), 2)]
    data = b''.join([int(x, 16).to_bytes(1, 'big') for x in bytes_])
    return data

assert parse_bytes_permissive('') == b''
assert parse_bytes_permissive('A') == b'\x0A'
assert parse_bytes_permissive('AB') == b'\xAB'
assert parse_bytes_permissive('ABC') == b'\x0A\xBC'
assert parse_bytes_permissive('ABCD') == b'\xAB\xCD'
assert parse_bytes_permissive(' A') == b'\x0A'
assert parse_bytes_permissive('   A  ') == b'\x0A'
assert parse_bytes_permissive('A   B ') == b'\xAB'
assert parse_bytes_permissive('  A B  ') == b'\xAB'
assert parse_bytes_permissive('   A B  C') == b'\x0A\xBC'
assert parse_bytes_permissive('   A B C  ') == b'\x0A\xBC'
assert parse_bytes_permissive('A BC   ') == b'\x0A\xBC'
assert parse_bytes_permissive('AB  C D') == b'\xAB\xCD'
assert parse_bytes_permissive(' A   BC D') == b'\xAB\xCD'
assert parse_bytes_permissive('  A B  C D') == b'\xAB\xCD'
assert parse_bytes_permissive(' ABCD  ') == b'\xAB\xCD'

# these are commands general enough to be handled in a way factored from each architecture repl
#
def general_handle_command(cmd, emulator, disassembler, addr, register_lookup):
    if cmd == 'r':
        return 'executed' # so caller will show context
    if cmd == 'q':
        return 'quit'

    if m := re.match(r'^echo (.*)$', cmd):
        message = m.group(1)
        print(colored(message, 'red'))
        return True

    # enter bytes, example:
    # eb 0 AA BB CC DD
    if m := re.match(r'eb ([a-fA-F0-9x]+) (.*)', cmd):
        (addr, bytestr) = m.group(1, 2)
        addr = int(addr, 16)
        data = parse_bytes_permissive(bytestr)
        print('writing:', colored(data.hex(), 'green'))
        emulator.mem_write(addr, data)
        return True

    # set register, example:
    # r pc = 0x10
    if m := re.match(r'(?:regset|r) ([^ ]+)\s*=\s*(.*)', cmd):
        rname, rval = m.group(1, 2)
        emulator.reg_write(register_lookup[rname], int(rval, 16))
        return True

    # reg write, example:
    # r3 = 0xDEADBEEF
    if m := re.match(r'([^\s]+)\s*=\s*(.+)', cmd):
        rname, rval = m.group(1, 2)
        if rname in register_lookup:
            emulator.reg_write(register_lookup[rname], int(rval, 16))
            return 'executed'
        else:
            print('ERROR: unknown register %s' % rname)
            return False

    # dump bytes, example:
    # db 0
    if m := re.match(r'db ([^L ]+)( L.*)?', cmd):
        addr = int(m.group(1), 16)
        length = 1*int(m.group(2)[2:], 16) if m.group(2) else 64
        data = emulator.mem_read(addr, length)
        print(get_hex_dump(data, addr, grouping=1))
        return True

    if m := re.match(r'dw ([^L ]+)( L.*)?', cmd):
        addr = int(m.group(1), 16)
        length = 2*int(m.group(2)[2:], 16) if m.group(2) else 64
        data = emulator.mem_read(addr, length)
        print(get_hex_dump(data, addr, grouping=2))
        return True

    if m := re.match(r'dd ([^L ]+)( L.*)?', cmd):
        addr = int(m.group(1), 16)
        length = 4*int(m.group(2)[2:], 16) if m.group(2) else 64
        data = emulator.mem_read(addr, length)
        print(get_hex_dump(data, addr, grouping=4))
        return True

    if m := re.match(r'dq ([^L ]+)( L.*)?', cmd):
        addr = int(m.group(1), 16)
        length = 8*int(m.group(2)[2:], 16) if m.group(2) else 64
        data = emulator.mem_read(addr, length)
        print(get_hex_dump(data, addr, grouping=8))
        return True

    # disassemble bytes, example:
    # u 0
    if m := re.match(r'u (.*)', cmd):
        addr = int(m.group(1),16)
        data = emulator.mem_read(addr, 64)
        for i in disassembler.disasm(data, addr):
            addr_str = '%08X' % i.address
            bytes_str = ' '.join(['%02X'%b for b in i.bytes]).ljust(2+1+2+1+2+1+2)
            print(f'{addr_str}: {bytes_str} {i.mnemonic} {i.op_str}')
        return True

    # anything bytes-like ends up being written and executed, example:
    # eb fe
    if m := re.match(r'^[a-fA-F0-9 ]+$', cmd):
        data = parse_bytes_permissive(cmd)
        emulator.mem_write(addr, data)
        addr_stop = addr + len(data)
        print(f'writing, executing [0x{addr:X}, 0x{addr_stop:X}): ', colored(data.hex(), 'green') + f' at 0x{addr:X}')
        emulator.emu_start(addr, addr_stop)
        return 'executed'

    # go
    if cmd in ['g', 'go', 'c', 'cont', 'continue']:
        pc = emulator.reg_read(UC_ARM_REG_PC)
        emulator.emu_start(pc, 0)
        return 'executed'

    # "monitor" commands
    # monitor map <addr> <length> <perms>
    if m := re.match(r'monitor map (.*) (.*) (.*)$', cmd):
        addr = int(m.group(1), 16)
        length = int(m.group(2), 16)
        perms = 0
        for c in m.group(3):
            if c in 'rR':
                perms |= UC_PROT_READ
            elif c in 'wW':
                perms |= UC_PROT_WRITE
            elif c in 'xX':
                perms |= UC_PROT_EXECUTE
        print(f'uc.mem_map(0x{addr:X}, 0x{length:X}, 0x{perms:X})')
        emulator.mem_map(addr, length, perms)
        return True

    return None

def assemble_command(asmstr, addr, uc, ks):
    encoding, count = None, None
    encoding, count = ks.asm(asmstr, addr=addr)
    data = b''.join([x.to_bytes(1, 'big') for x in encoding])
    print(f'assembled {addr:08X}: {colored(data.hex(), "green")} ({len(encoding)} bytes)')
    uc.mem_write(addr, data)
    uc.emu_start(addr, addr + len(data))
    return 'executed'

# hi and lo are inclusive, eg: 4,0 means gets b4...b0 (5 bits total)
def get_bits(value, hi, lo=None):
    if lo == None:
        lo = hi
    width = hi - lo + 1
    mask = (1<<(hi+1))-1
    return (value & mask) >> lo

#foo = 0b10101010101010101010101010101010
#assert get_bits(foo, 0, 0) == 0
#assert get_bits(foo, 1, 1) == 1
#assert get_bits(foo, 2, 2) == 0
#assert get_bits(foo, 3, 3) == 1
#assert get_bits(foo, 31, 31) == 1
#assert get_bits(foo, 30, 30) == 0
#assert get_bits(foo, 29, 29) == 1
#assert get_bits(foo, 28, 28) == 0
#assert get_bits(foo, 1, 0) == 0b10
#assert get_bits(foo, 2, 0) == 0b010
#assert get_bits(foo, 3, 0) == 0b1010
#assert get_bits(foo, 4, 0) == 0b01010
#assert get_bits(foo, 5, 0) == 0b101010
#assert get_bits(foo, 6, 0) == 0b0101010
#assert get_bits(foo, 7, 0) == 0b10101010
#assert get_bits(foo, 7, 1) == 0b1010101
#assert get_bits(foo, 7, 2) == 0b101010
#assert get_bits(foo, 7, 3) == 0b10101
#assert get_bits(foo, 7, 4) == 0b1010
#assert get_bits(foo, 7, 5) == 0b101
#assert get_bits(foo, 7, 6) == 0b10
#assert get_bits(foo, 7, 7) == 0b1
