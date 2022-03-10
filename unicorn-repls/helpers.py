import struct

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
