import os, sys, re

import gdb

seen = set()
queue = []

def queue_add(type_name):
    global seen, queue

    if type_name in seen:
        return
    seen.add(type_name)

    ignore = ['_Bool', 'char', 'int', 'long', 'float', 'double',
        'long double', 'long long', 'unsigned long long', 'unsigned long',
        'short', 'unsigned short', 'signed char', 'unsigned char',
        'unsigned int', '__int128', '__int128 unsigned', 'long unsigned int']

    if type_name in ignore:
        print('<!-- "%s" is in ignore list -->' % type_name)
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
    indent = '  '*depth

    # start XML tag
    tcode = type_code_tostr(t.code)
    result = '%s<%s' % (indent, tcode)

    # add attributes
    type_name = get_type_name(t)
    if type_name:
        result += ' tname="%s"' % type_name
    if var_name:
        result += ' vname="%s"' % var_name
    if t.code == gdb.TYPE_CODE_ARRAY:
        result += ' size="%d"' % array_size(t)


    # end XML tag
    if t.code in [gdb.TYPE_CODE_INT]:
        result += ' />\n'
        return result
    else:
        result += '>\n'

    # enqueue others
    if type_name:
        queue_add(type_name)

    if not (type_name and stop_at_first_named):
        #if t.code in [gdb.TYPE_CODE_UNION]:
        #    breakpoint()
        if t.code in [gdb.TYPE_CODE_UNION, gdb.TYPE_CODE_STRUCT]:
            for field in t.fields():
                result += process_type(field.type, field.name, depth+1, True)
        elif t.code in [gdb.TYPE_CODE_ENUM]:
            for field in t.fields():
                result += '%s<FIELD name="%s" val="%s" />\n' % ('  '*(depth+1), field.name, field.enumval)
        elif t.code in [gdb.TYPE_CODE_TYPEDEF, gdb.TYPE_CODE_ARRAY, gdb.TYPE_CODE_PTR]:
            result += process_type(t.target(), None, depth+1, True)
        elif t.code == gdb.TYPE_CODE_FUNC:
            # return type
            result += process_type(t.target(), None, depth+1, False)
            # arguments
            for field in t.fields():
                result += process_type(field.type, field.name, depth+1, True)

    result += '%s</%s>\n' % (indent, tcode)
    return result

if 0:
    print('<?xml version="1.0" encoding="UTF-8"?>')
    print('<types>')

    queue = ['__gconv_fct']
    queue = ['struct r_debug']
    #queue_add('__mbstate_t')
    while queue:
        target = queue.pop()

        try:
            mytype = gdb.lookup_type(target)
        except gdb.error as e:
            print('<!-- "%s" errored in gdb -->' % str(e))
            continue

        #print_basic_info(mytype)
        print(process_type(mytype))

    print('</types>')
    gdb.execute('q')

#
# loop over all data returned from "info functions"
#
named_objects = []
lines = [x.rstrip() for x in gdb.execute('info functions', False, True).split('\n')]
for line in lines:
    if not line or line.isspace(): continue
    if line.startswith('File '): continue
    if line.startswith('All defined functions:'): continue
    m = re.search(r'^.*?(\w+)\(', line)
    if not m:
        print('wtf: %s' % line)
    func_name = m.group(1)
    func_val = gdb.parse_and_eval(func_name)
    result = process_type(func_val.type, func_name)
    named_objects.append(result)

#
# loop over all data returned from "info types"
#
named_types = []
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
        #print('looking up %s' % line[0:-1])
        result = process_type(gdb.lookup_type(line[0:-1]))
        named_types.append(result)
        continue

    # typedef struct {\n ... \n} foo;
    m = re.match(r'^typedef (struct|union) {', line)
    if m:
        # search for end of typedef
        name = ''
        while not re.match(r'^} (\w+);', lines[i]):
            i += 1
        name = re.match(r'^} (\w+);', lines[i]).group(1)
        result = process_type(gdb.lookup_type(name))
        named_types.append(result)
        i += 1;
        continue

    # typedef ... foo;
    m = re.match(r'^typedef .* (\w+);$', line)
    if m:
        name = m.group(1)
        result = process_type(gdb.lookup_type(name))
        named_types.append(result)
        continue

    # enumerations
    m = re.match(r'^enum (\w+);$', line)
    if m:
        result = process_type(gdb.lookup_type(line[0:-1]))
        named_types.append(result)
        continue

    raise Exception('dunno how to handle line: %s' % line)

with open('/tmp/tmp.xml', 'w') as fp:
    fp.write('<?xml version="1.0" encoding="UTF-8"?>\n')
    fp.write('<type_library>\n')

    fp.write('<!-- %d named objects -->\n' % len(named_objects))
    fp.write('<named_objects>\n')
    for result in named_objects:
        fp.write(result)
    fp.write('</named_objects>\n')

    fp.write('<!-- %d named types -->\n' % len(named_types))
    fp.write('<named_types>\n')
    for result in named_types:
        fp.write(result)
    fp.write('</named_types>\n')

    fp.write('</type_library>')

gdb.execute('q')
