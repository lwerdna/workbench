import os, sys, re

import gdb

seen = set()
queue = []

def queue_add(type_name):
    global seen, queue

    if type_name in seen:
        return
    seen.add(type_name)

    exceptions = ['_Bool', 'char', 'int', 'long', 'float', 'double',
        'long double', 'long long', 'unsigned long long', 'unsigned long',
        'short', 'unsigned short', 'signed char', 'unsigned char',
        'unsigned int', '__int128', '__int128 unsigned']

    if type_name in exceptions:
        print('// %s is in exceptions' % type_name)
        return

    queue = [type_name] + queue

def type_code_tostr(code):
    if code==gdb.TYPE_CODE_PTR: return 'PTR'
    if code==gdb.TYPE_CODE_ARRAY: return 'ARRAY'
    if code==gdb.TYPE_CODE_STRUCT: return 'STRUCT'
    if code==gdb.TYPE_CODE_UNION: return 'UNION'
    if code==gdb.TYPE_CODE_ENUM: return 'ENUM'
    if code==gdb.TYPE_CODE_FLAGS: return 'FLAGS'
    if code==gdb.TYPE_CODE_FUNC: return 'FUNC'
    if code==gdb.TYPE_CODE_INT: return 'INT'
    if code==gdb.TYPE_CODE_FLT: return 'FLT'
    if code==gdb.TYPE_CODE_VOID: return 'VOID'
    if code==gdb.TYPE_CODE_SET: return 'SET'
    if code==gdb.TYPE_CODE_RANGE: return 'RANGE'
    if code==gdb.TYPE_CODE_STRING: return 'STRING'
    if code==gdb.TYPE_CODE_BITSTRING: return 'BITSTRING'
    if code==gdb.TYPE_CODE_ERROR: return 'ERROR'
    if code==gdb.TYPE_CODE_METHOD: return 'METHOD'
    if code==gdb.TYPE_CODE_METHODPTR: return 'METHODPTR'
    if code==gdb.TYPE_CODE_MEMBERPTR: return 'MEMBERPTR'
    if code==gdb.TYPE_CODE_REF: return 'REF'
    if code==gdb.TYPE_CODE_CHAR: return 'CHAR'
    if code==gdb.TYPE_CODE_BOOL: return 'BOOL'
    if code==gdb.TYPE_CODE_COMPLEX: return 'COMPLEX'
    if code==gdb.TYPE_CODE_TYPEDEF: return 'TYPEDEF'
    if code==gdb.TYPE_CODE_NAMESPACE: return 'NAMESPACE'
    if code==gdb.TYPE_CODE_DECFLOAT: return 'DECFLOAT'
    if code==gdb.TYPE_CODE_INTERNAL_FUNCTION: return 'INTERNAL_FUNCTION'
    return None

def type_test_base(t):
    return t.code in [gdb.TYPE_CODE_INT, gdb.TYPE_CODE_CHAR]

def type_test_fields(t):
    # gdb.TYPE_CODE_ENUM too, but we don't have to recur on those types
    return t.code in [gdb.TYPE_CODE_STRUCT, gdb.TYPE_CODE_UNION, gdb.TYPE_CODE_FUNC]

def type_test_funcptr(t):
    return t.code == gdb.TYPE_CODE_PTR and t.target().code == gdb.TYPE_CODE_FUNC

def array_size(t):
    if not t.code == gdb.TYPE_CODE_ARRAY:
        return None
    r = t.range()
    return r[1]-r[0]+1

# can this type be referred to by name later?
#
# "typedef int foo;"           -> YES, "foo" is the name of a type
# "unsigned long;"             -> YES, "unsigned long" is the name of a type
# struct foo {int A; int B;};  -> YES, "struct foo" is the name of a type
# enum {A=1,B=2} foo;"         -> NO, anonymous enum applied to variable foo
# struct {int A; int B;"} foo; -> NO, anonymous struct applied to variable foo
#
def get_type_name(t):
    if not t:
        return None
    if t.code == gdb.TYPE_CODE_STRUCT:
        if not t.tag: return None
        return 'struct ' + t.tag
    if t.code == gdb.TYPE_CODE_UNION:
        if not t.tag: return None
        return 'union ' + t.tag
    if t.code == gdb.TYPE_CODE_ENUM:
        if not t.tag: return None
        return 'enum ' + t.tag
    return t.name


def process_type(t, var_name=None, depth=0, stop_at_first_named=False):
    def indent(d=depth):
        return '  '*d

    result = ''

    tmp = '%s%s\n' % (indent(), type_code_tostr(t.code))
    result += tmp

    type_name = get_type_name(t)
    if type_name:
        result += '%s.tname="%s"\n' % (indent(depth+1), type_name)
    if var_name:
        result += '%s.vname="%s"\n' % (indent(depth+1), var_name)

    tmp += ' "%s"' % (type_name) if type_name else ' ""'
    tmp += ' "%s"' % (var_name) if var_name else ' ""'
    tmp += '\n'

    if t.code == gdb.TYPE_CODE_ARRAY:
        result += '%s.size=%d\n' % (indent(depth+1), array_size(t))

    if type_name:
        queue_add(type_name)
        if stop_at_first_named:
            return result

    #if t.code in [gdb.TYPE_CODE_UNION]:
    #    breakpoint()
    if t.code in [gdb.TYPE_CODE_UNION, gdb.TYPE_CODE_STRUCT, gdb.TYPE_CODE_ENUM]:
        for field in t.fields():
            result += process_type(field.type, field.name, depth+1, True)
    elif t.code in [gdb.TYPE_CODE_TYPEDEF, gdb.TYPE_CODE_ARRAY, gdb.TYPE_CODE_PTR]:
        result += process_type(t.target(), None, depth+1, True)
    elif t.code == gdb.TYPE_CODE_FUNC:
        # return type
        result += process_type(t.target(), None, depth+1, False)
        # arguments
        for field in t.fields():
            result += process_type(field.type, field.name, depth+1, True)

    return result

def print_basic_info(mytype):
    print('str(mytype): %s' % str(mytype))
    print('mytype.code: %s' % type_code_tostr(mytype.code))
    print('mytype.name: %s' % mytype.name)
    print('mytype.tag: %s' % mytype.tag)
    if type_test_fields(mytype):
        print('mytype.fields: %s' % mytype.fields())
    if mytype.code in [gdb.TYPE_CODE_TYPEDEF, gdb.TYPE_CODE_PTR]:
        print('dereferencing type...')
        print_basic_info(mytype.target())

#targets = ['struct tzstring_l']
if 1:
    #queue = ['__gconv_fct']
    queue_add('__mbstate_t')
    while queue:
        target = queue.pop()

        try:
            mytype = gdb.lookup_type(target)
        except gdb.error as e:
            print('// %s' % str(e))
            continue

        #print_basic_info(mytype)
        print(process_type(mytype))

    gdb.execute('q')

#
# loop over all data returned from "info types"
#
lines = [x.rstrip() for x in gdb.execute('info types', False, True).split('\n')]
i = 0
while i<len(lines):
    line = lines[i]
    i += 1
    # ignore list
    if not line or line.isspace(): continue
    if line.startswith('All defined type'): continue
    if line.startswith('File '): continue
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
    if line.startswith('typedef __int128;'): continue
    if line.startswith('typedef __int128 unsigned;'): continue

    # terminating condition
    if line.startswith('Non-debugging symbols'): break

    # struct foo;
    # union foo;
    m = re.match(r'^(struct|union) (\w+);$', line)
    if m:
        process_type(gdb.lookup_type(line[0:-1]))
        continue

    # typedef struct {\n ... \n} foo;
    m = re.match(r'^typedef (struct|union) {', line)
    if m:
        # search for end of typedef
        name = ''
        while not re.match(r'^} (\w+);', lines[i]):
            i += 1
        name = re.match(r'^} (\w+);', lines[i]).group(1)
        process_type(gdb.lookup_type(name))
        i += 1;
        continue

    # typedef ... foo;
    m = re.match(r'^typedef .* (\w+);$', line)
    if m:
        name = m.group(1)
        process_type(gdb.lookup_type(name))
        continue

    # enumerations
    m = re.match(r'^enum (\w+);$', line)
    if m:
        process_type(gdb.lookup_type(line[0:-1]))
        continue

    raise Exception('dunno how to handle line: %s' % line)


#print('digraph MyGraph {')
#for edge in graph_edges:
#    print(edge)
#print('}')


with open('/tmp/tmp.c', 'w') as fp:
    for (i, (name,decl)) in enumerate(declarations.items()):
        fp.write('// declaration #%d of %s\n' % (i, name))
        fp.write(decl + ';\n')



gdb.execute('q')
