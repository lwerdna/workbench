# capture the idea of C struct in python lists

import struct

#------------------------------------------------------------------------------
# main API
#------------------------------------------------------------------------------

# read lstruct
def lstruct_read(ls, inferior, addr):
    for entry in ls:
        if len(entry) == 2:
            name, sublist = entry
            advance_by = lstruct_len(sublist)
            lstruct_read(sublist, inferior, addr)
        else:
            name, length, formatter = entry
            data = inferior.read_memory(addr, length).tobytes()
            entry.extend([addr, data])
            advance_by = length
        
        addr += advance_by

# measure length of lstruct
def lstruct_len(ls):
    result = 0

    for entry in ls:
        if len(entry) == 2:
            name, sublist = entry
            result += lstruct_len(sublist)
        else:
            result += entry[1]

    return result

def lstruct_str(ls, depth=0):
    indent = '  '*depth
    lines = []

    for entry in ls:
        if len(entry) == 2:
            name, sublist = entry
            lines.append(f'{indent}{name}:\n' + lstruct_str(sublist, depth+1))
        else:
            name, x, formatter, addr, data = entry
            lines.append(f'{indent}{name}: ' + formatter(data))

    return '\n'.join(lines)

def lstruct_print(ls):
    print(lstruct_str(ls))

#------------------------------------------------------------------------------
# formatters
#------------------------------------------------------------------------------
def as_string(data):
    return ''.join(chr(x) for x in data)

def as_016x(data):
    return hex(struct.unpack('<Q', data)[0])

def as_08x(data):
    return hex(struct.unpack('<I', data)[0])

def as_16d(data):
    return str(struct.unpack('<Q', data)[0])
