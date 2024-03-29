import os, sys, re

import gdb

graph_edges = set()

# name: declaration
# eg: 'foo'; 'typedef int *foo'
# eg: 'unsigned int':
# eg: 'struct foo': 'struct foo {int A; intB;};'
declarations = {}

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
    assert t.code == gdb.TYPE_CODE_ARRAY
    r = t.range()
    return r[1]-r[0]+1

# compute the C syntax for a type with a variable
# 'unsigned char [16]' + 'foo' = 'unsigned char foo[16]'
def define(declare_str, varname):
    # arrays
    # 'int [5]', 'foo' -> 'int foo[5]'
    m = re.match(r'^(.*) (\[\d+\])$', declare_str)
    if m:
        return '%s %s%s' % (m.group(1), varname, m.group(2))
   
    # function pointers
    # 'int (*)(int)', 'foo' -> 'int (*foo)(int)'
    m = re.match(r'^(.*)\(\*\)(.*)', declare_str)
    if m:
        return '%s (*%s)%s' % (m.group(1), varname, m.group(2))

    return '%s %s' % (declare_str, varname)
    
# can this type be referred to by name later?
#
# "typedef int foo;"           -> YES, "foo" is the name of a type
# "unsigned long;"             -> YES, "unsigned long" is the name of a type
# struct foo {int A; int B;};  -> YES, "struct foo" is the name of a type
# enum {A=1,B=2} foo;"         -> NO, anonymous enum applied to variable foo
# struct {int A; int B;"} foo; -> NO, anonymous struct applied to variable foo
#
def full_name(t):
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

def log_edge(a, b):
    global graph_edges
    src = full_name(a)
    if not src: src = str(a)
    dst = full_name(b)
    if not dst: dst = str(b)
    if not (src and dst):
        return
    edge_text = '"%s" -> "%s"' % (src, dst)
    if edge_text in graph_edges:
        return
    graph_edges.add(edge_text)

# recursively traverse type tree, adding to global declarations
# return code that can be used to declare a variable of this type
#
# examples for named types:
#   "unsigned char"
#   "int"
#   "struct mystruct"
# examples for anonymous types:
#   "struct {int A; int B;}"
#   "union {int A; int B;}"
#
def process_type(t, trail=[]):
    global declarations

    #print('// process_type(%d (%s))' % (t.code, type_code_tostr(t.code)))

    fn = full_name(t)

    # already processed? out!
    if fn:
        if fn in declarations:
            #print('// already processed "%s"' % fn)
            return fn
   
    # prevent traversing recursively
    if fn and (fn in trail or (t.code==gdb.TYPE_CODE_PTR and full_name(t.target()) in trail)):
        #print('// stop recursion due to "%s"' % fn)
        return fn

    if t.code == gdb.TYPE_CODE_UNION:
        lines = []
        for field in t.fields():
            ftype = field.type
            declare_str = process_type(ftype, trail+[fn])
            lines.append('%s;' % define(declare_str, field.name))
        declaration = 'union %s {%s}' % (t.tag or '', ' '.join(lines))

        if fn:
            declarations[fn] = declaration
            return fn
        else:
            return declaration

    if t.code == gdb.TYPE_CODE_STRUCT:
        lines = ['struct %s {' % (t.tag or '')]
        for field in t.fields():
            ftype = field.type
            #log_edge(t,  ftype)
            declare_str = process_type(ftype, trail+[fn])
            lines.append('\t%s;' % define(declare_str, field.name))
        lines.append('}')
        declaration = '\n'.join(lines)

        if fn:
            declarations[fn] = declaration
            return fn
        else: 
            # anonymous, so the full declaration is needed each time
            return declaration

    elif t.code == gdb.TYPE_CODE_TYPEDEF:
        assert t.name == fn
        target = t.target()
        #log_edge(t, target)
        subdecl = process_type(target, trail+[fn])
        declaration = 'typedef ' + define(subdecl, t.name)
        declarations[fn] = declaration
        return fn

    elif t.code == gdb.TYPE_CODE_ARRAY:
        target = t.target()
        #log_edge(t, target)
        declaration = '%s [%d]' % (process_type(target, trail+[fn]), array_size(t))
        # arrays of existing types don't add any new type names
        return declaration

    elif t.code == gdb.TYPE_CODE_PTR:
        target = t.target()
        #log_edge(t, target)
        # pointers to existing types don't add any new type names
        tmp = process_type(target, trail+[fn])
        
        # function types like "int (*)(int, int)" already have star
        if target.code == gdb.TYPE_CODE_FUNC:
            return tmp;

        return tmp + ' *'

    elif t.code == gdb.TYPE_CODE_ENUM:
        lines = []
        for field in t.fields():
            lines.append('%s=%s' % (field.name, field.enumval))
        declaration = 'enum %s { %s }' % ((t.tag or ''), ','.join(lines))

        if fn:
            declarations[fn] = declaration
            return fn
        else:
            return declaration

    elif t.code == gdb.TYPE_CODE_FUNC:
        # return type
        declaration = ''
        return_type = t.target()
        #log_edge(t, return_type)
        declaration += process_type(return_type, trail+[fn])
        declaration += ' (*)('
        # arguments
        lines = []
        for field in t.fields():
            field_type = field.type
            #log_edge(t, field_type)
            lines.append(process_type(field_type, trail+[fn]))
        declaration = ','.join(lines) + ')'
        return declaration

    else:
        #print('// returning default full_name()=%s for type code %d (%s)' % (fn, t.code, type_code_tostr(t.code)))
        return fn

def emit_all_declarations():
    global declarations

    # forward declare all structs
    for name in declarations.keys():
        if name.startswith('struct '):
            print(name + ';')

    for (i, (name,decl)) in enumerate(declarations.items()):
        print('// declaration #%d of %s' % (i, name))
        print(decl + ';')

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
    targets = ['__gconv_fct']
    targets = ['_IO_close_t']
    targets = ['struct argp']
    targets = ['struct _IO_marker']
    #targets = ['struct argp_option']
    targets = ['_IO_finish_t']
    targets = ['__gconv_fct']

    for target in targets:
        mytype = gdb.lookup_type(target)
        print_basic_info(mytype)
        ptr = process_type(mytype)
        print('process_type returned: ', str(ptr))
                
    #print('digraph MyGraph {')
    #for edge in graph_edges:
    #    print(edge)
    #print('}')
    #gdb.execute('q')

    emit_all_declarations()
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
