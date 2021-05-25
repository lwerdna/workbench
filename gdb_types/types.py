import os, sys, re

import gdb

def get_struct_def(name):
    # ptype alone will leave things beyond a certain depth unprinted, like "{...}"
    # use ptype/o (flag: offset) and remove comments instead...
    output = gdb.execute('ptype/o struct '+name, False, True).rstrip()
    lines = output.split('\n')
    assert 'type =' in lines[0], 'wtf: %s' % lines[0]
    lines[0] = lines[0].replace('type = ', '')
    lines = [l.rstrip() for l in lines]
    lines = [re.sub('/\*.*?\*/', '', l) for l in lines]
    lines = [l for l in lines if (l and not l.isspace())]
    return '\n'.join(lines) + ';\n'

def get_typedef_struct_def(name):
    output = gdb.execute('ptype/o '+name, False, True).rstrip()
    lines = output.split('\n')
    assert 'type =' in lines[0], 'wtf: %s' % lines[0]
    lines[0] = lines[0].replace('type = ', 'typedef ')
    lines = [l.rstrip() for l in lines]
    lines = [re.sub('/\*.*?\*/', '', l) for l in lines]
    lines = [l for l in lines if (l and not l.isspace())]
    return '\n'.join(lines) + ' ' + name + ';\n'

def get_enum_def(name):
    output = gdb.execute('ptype enum '+name, False, True).rstrip()
    if output.startswith('type = '):
        output = output[7:]
    return output + ';\n'

lines = gdb.execute('info types', False, True).split('\n')

memory = set()
with open('/tmp/tmp.c', 'w') as fp:
    i = 0
    while i<len(lines):
        line = lines[i]
        i += 1

        # ignore list
        if not line or line.isspace(): continue
        if line.startswith('All defined type'): continue
        if line.startswith('File '):
            fp.write('// %s\n' % line)
            continue
        if line.startswith('typedef _Bool;'): continue
        if line.startswith('typedef char;'): continue
        if line.startswith('typedef int;'): continue
        if line.startswith('typedef long;'): continue
        if line.startswith('typedef float;'): continue
        if line.startswith('typedef double;'): continue
        if line.startswith('typedef long double;'): continue
        if line.startswith('typedef long long;'): continue
        if line.startswith('typedef unsigned long long;'): continue
        if line.startswith('typedef unsigned long;'): continue
        if line.startswith('typedef short;'): continue
        if line.startswith('typedef unsigned short;'): continue
        if line.startswith('typedef signed char;'): continue
        if line.startswith('typedef unsigned char;'): continue
        if line.startswith('typedef unsigned int;'): continue
        if line.startswith('typedef __int128 unsigned;'): continue

        # terminating condition
        if line.startswith('Non-debugging symbols'): break

        # struct foo;
        m = re.match(r'^struct (\w+);$', line)
        if m:
            if line in memory:
                fp.write('// skipping second instance of: %s\n' % line)
                continue
            memory.add(line)
            fp.write('// %s\n' % line)
            name = m.group(1)
            fp.write(get_struct_def(m.group(1)))
            continue

        # typedef struct {\n ... \n} foo; 
        m = re.match(r'^typedef struct {', line)
        if m:
            # search for end of typedef
            name = ''
            while not re.match(r'^} (\w+);', lines[i]):
                i += 1
            name = re.match(r'^} (\w+);', lines[i]).group(1)
            fp.write(get_typedef_struct_def(name))
            i += 1
            continue

        # enumerations get expanded
        m = re.match(r'^enum (\w+);$', line)
        if m:
            if line in memory:
                fp.write('// skipping second instance of: %s\n' % line) 
                continue
            memory.add(line)
            fp.write('// %s\n' % line)
            name = m.group(1)
            fp.write(get_enum_def(m.group(1)))
            continue

        fp.write(line + '\n')

gdb.execute('q')
