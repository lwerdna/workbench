import re
import struct

from termcolor import colored

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
def general_handle_command(cmd, mu, addr, register_lookup):
    if cmd == 'r':
        return 'executed' # so caller will show context
    if cmd == 'q':
        return 'quit'

    # enter bytes, example:
    # eb 0 AA BB CC DD
    if m := re.match(r'eb ([a-fA-F0-9x]+) (.*)', cmd):
        (addr, bytestr) = m.group(1, 2)
        addr = int(addr, 16)
        data = parse_bytes_permissive(bytestr)
        print('writing:', colored(data.hex(), 'green'))
        mu.mem_write(addr, data)
        return True

    # set register, example:
    # r pc = 0x10
    if m := re.match(r'(?:regset|r) ([^ ]+)\s*=\s*(.*)', cmd):
        (rname, rval) = m.group(1, 2)
        mu.reg_write(register_lookup[rname], int(rval, 16))
        return True

    # dump bytes, example:
    # db 0
    if m := re.match(r'db (.*)', cmd):
        addr = int(m.group(1),16)
        data = mu.mem_read(addr, 64)
        print(get_hex_dump(data, addr))
        return True

    # anything bytes-like ends up being written and executed, example:
    # eb fe
    if m := re.match(r'^[a-hA-H0-9 ]+$', cmd):
        data = parse_bytes_permissive(cmd)
        print('writing:', colored(data.hex(), 'green'))
        mu.mem_write(addr, data)
        mu.emu_start(addr, addr + len(data))
        return 'executed'

    return None

def assemble_command(asmstr, addr, mu, ks):
    encoding, count = None, None
    encoding, count = ks.asm(asmstr, addr=addr)
    data = b''.join([x.to_bytes(1, 'big') for x in encoding])
    print(f'assembled {addr:08X}: {colored(data.hex(), "green")} ({len(encoding)} bytes)')
    mu.mem_write(addr, data)
    mu.emu_start(addr, addr + len(data))
    return 'executed'

