# run this from lldb with (lldb) script
# >>> import dumptypes; import importlib; importlib.reload(dumptypes); dumptypes.dump(lldb.target)

from lldb import *

def typeclass2str(tc):
    return {
        eTypeClassInvalid: 'Invalid',
        eTypeClassArray: 'Array',
        eTypeClassBlockPointer: 'BlockPointer',
        eTypeClassBuiltin: 'Builtin',
        eTypeClassClass: 'Class',
        eTypeClassComplexFloat: 'ComplexFloat',
        eTypeClassComplexInteger: 'ComplexInteger',
        eTypeClassEnumeration: 'Enumeration',
        eTypeClassFunction: 'Function',
        eTypeClassMemberPointer: 'MemberPointer',
        eTypeClassObjCObject: 'ObjCObject',
        eTypeClassObjCInterface: 'ObjCInterface',
        eTypeClassObjCObjectPointer: 'ObjCObjectPointer',
        eTypeClassPointer: 'Pointer',
        eTypeClassReference: 'Reference',
        eTypeClassStruct: 'Struct',
        eTypeClassTypedef: 'Typedef',
        eTypeClassUnion: 'Union',
        eTypeClassVector: 'Vector',
        eTypeClassOther: 'Other',
        eTypeClassAny: 'Any'}[tc]

def print_type_verbose(t:SBType):
    print(t)
    print('typeclass: %s' % typeclass2str(t.GetTypeClass()))
    print('IsAnonymousType(): %s' % t.IsAnonymousType())
    print('IsArrayType(): %s' % t.IsArrayType())
    print('IsFunctionType(): %s' % t.IsFunctionType())
    print('IsPointerType(): %s' % t.IsPointerType())
    print('IsPolymorphicClass(): %s' % t.IsPolymorphicClass())
    print('IsReferenceType(): %s' % t.IsReferenceType())
    print('IsTypeComplete(): %s' % t.IsTypeComplete())
    print('IsTypedefType(): %s' % t.IsTypedefType())
    print('IsValid(): %s' % t.IsValid())
    print('IsVectorType(): %s' % t.IsVectorType())

def declaration_from_type_and_name(t:SBType, varname):
    tc = t.GetTypeClass()

    # int foo; char foo; etc.
    if tc == eTypeClassBuiltin:
        return '%s %s;' % (t.name, varname)
    else:
        raise Exception('unsupported type class %d (%s)' % (tc, typeclass2str(tc)))

# 'struct foo { int a; int b;}' ->
# 'struct foo {
#     int a;
#     int b;
# };'
def beautify(s):
    result = []
    depth = 0
    for c in s:
        if c == '{':
            depth += 1
            result.append('{\n')
            result.append('    '*depth)
        elif c == ';':
            result.append(';\n')
            result.append('    '*depth)
        elif c == '}':
            result.pop()
            result.append('}')
        else:
            result.append(c)
    return ''.join(result)

def type_to_c(t:SBType):
    result = ''

    tc = t.GetTypeClass()
    if tc == eTypeClassStruct:
        result = 'struct %s {' % t.name
        for field in t.fields:
            result += declaration_from_type_and_name(field.type, field.name)
        result += '};'
    elif tc == eTypeClassBuiltin:
        result = '%s;' % t.name
    elif tc == eTypeClassFunction:
        breakpoint()
    else:
        raise Exception('unsupported type class %d (%s)' % (tc, typeclass2str(tc)))

    return result

def dump(target):
    for module in target.modules:
        print(module)

    module = target.GetModuleAtIndex(0)

    mask = eTypeClassArray | eTypeClassBuiltin | eTypeClassEnumeration | eTypeClassFunction | \
        eTypeClassPointer | eTypeClassReference | eTypeClassStruct | eTypeClassTypedef | eTypeClassUnion

    types:SBTypeList = module.GetTypes(mask)
    # t:SBType
    for t in types:
        print_type_verbose(t)
        print(beautify(type_to_c(t)))
    #print('module: %s' % (module.file))
    #types = module.GetTypes(eTypeClassClass | eTypeClassStruct)
    #print('Found %u types in "%s"' % (len(types), module.file))

# run this with:
# import importlib; importlib.reload(dumptypes); dumptypes.hello_world()
def hello_world():
    print('hello, world!')

# from https://lldb.llvm.org/use/python-reference.html
# import importlib; importlib.reload(dumptypes); dumptypes.test(lldb.process)
def test(process):
    # Print some simple process info
    print('test() here')
    print(process)
    state = process.GetState()
    print(process)
    if state == eStateStopped:
        # Get the first thread
        thread = process.GetThreadAtIndex (0)
        if thread:
            # Print some simple thread info
            print(thread)
            # Get the first frame
            frame = thread.GetFrameAtIndex (0)
            if frame:
                # Print some simple frame info
                print(frame)
                function = frame.GetFunction()
                # See if we have debug info (a function)
                if function:
                    # We do have a function, print some info for the function
                    print(function)
                    # Now get all instructions for this function and print them
                    target = process.GetTarget()
                    insts = function.GetInstructions(target)
                    for i in insts:
                        print(i)
                else:
                    # See if we have a symbol in the symbol table for where we stopped
                    symbol = frame.GetSymbol();
                    if symbol:
                        # We do have a symbol, print some info for the symbol
                        print(symbol)

