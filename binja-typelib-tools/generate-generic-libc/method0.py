#!/usr/bin/env python

# resources:
# https://en.wikibooks.org/wiki/C_Programming/Standard_library_reference

import pprint

import binaryninja
from binaryninja.enums import NamedTypeReferenceClass
from binaryninja.types import Type, NamedTypeReferenceType, StructureBuilder, EnumerationBuilder

def tokenize(line):
    result = []
    current_token = ''

    # inner/nested function
    def save():
        nonlocal current_token
        if current_token:
            result.append(current_token)
            current_token = ''

    for c in line:
        if c in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_':
            current_token += c
        elif c in '()*,;':
            save()
            result.append(c)
        elif c == ' ':
            save()
        else:
            raise Exception(f'unexpected character "{c}"')

    save()

    return result

def parse_func_prototype(line):
    result = {'return_type':[], 'name':'', 'params':[]}

    qualifiers = ['const', 'signed', 'unsigned', 'long']
    known_types = ['void', 'int', 'char', 'size_t', 'wchar_t', 'wint_t', 'wctype_t', 'double', 'div_t', 'ldiv_t', 'FILE', 'fpos_t']

    tokens = tokenize(line)

    while tokens[0] in qualifiers + known_types + ['*']:
        result['return_type'].append(tokens.pop(0))

    result['name'] = tokens.pop(0)

    assert tokens[0] == '(', breakpoint()

    if tokens == ['(', 'void', ')', ';']:
        return result

    tokens.pop(0)
    while tokens[0] != ';':
        group = []
        while not tokens[0] in [',', ')']:
            group.append(tokens.pop(0))

        if not group:
            tokens.pop(0)
            continue

        param_name = group[-1]
        if param_name in qualifiers + known_types + ['*']:
            raise Exception('unnamed parameter')

        result['params'].append(
            {
                'name': group[-1],
                'type': group[0:-1]
            }
        )

    return result

def convert(arch, tstring):
    if type(tstring) == list:
        tstring = ' '.join(tstring)

    if tstring in ['wchar_t', 'wint_t', 'size_t', 'int8_t', 'int16_t', 'int32_t', 'uint8_t', 'uint16_t', 'uint32_t', 'schar_t', 'wctype_t']:
        return NamedTypeReferenceType.create(named_type_class=NamedTypeReferenceClass.TypedefNamedTypeClass, guid=None, name=tstring)

    match tstring:
        case 'char': return Type.int(1)
        case 'char *': return Type.pointer(arch, Type.int(1))
        case 'char * *': return Type.pointer(arch, Type.pointer(arch, Type.int(1)))
        case 'const char *': return Type.pointer(arch, Type.int(1), True)
        case 'const fpos_t *': return Type.pointer(arch, Type.void(), True)
        case 'const void *': return Type.pointer(arch, Type.void(), True)
        case 'const void *': return Type.pointer(arch, Type.void(), True)
        case 'const wchar_t *': return Type.pointer(arch, convert(arch, 'wchar_t'), True)
        case 'div_t': return NamedTypeReferenceType.create(named_type_class=NamedTypeReferenceClass.StructNamedTypeClass, guid=None, name='div_t')
        case 'double': return Type.float(4)
        case 'fpos_t *': return Type.pointer(arch, Type.void())
        case 'FILE *': return Type.pointer(arch, Type.void())
        case 'int': return Type.int(arch.default_int_size, True)
        case 'int *': return Type.pointer(arch, Type.int(arch.default_int_size, True))
        case 'ldiv_t': return NamedTypeReferenceType.create(named_type_class=NamedTypeReferenceClass.StructNamedTypeClass, guid=None, name='ldiv_t')
        case 'long int': return Type.int(arch.default_int_size, True)
        case 'schar_t *': return Type.pointer(arch, convert(arch, 'schar_t'))
        case 'unsigned int': return Type.int(arch.default_int_size, False)
        case 'unsigned int *': return Type.pointer(arch, Type.int(arch.default_int_size, False))
        case 'unsigned long int': return Type.int(arch.default_int_size, False)
        case 'wchar_t *': return Type.pointer(arch, convert(arch, 'wchar_t'))
        case 'void': return Type.void()
        case 'void *': return Type.pointer(arch, Type.void())
        case _:
            print(f'ERROR: {tstring}')
            breakpoint()
            pass

if __name__ == '__main__':
    # read prototypes from header
    lines = [l.strip() for l in open('prototypes.h').readlines()]

    # prepare binja
    arch = binaryninja.Architecture['nanomips']
    typelib = binaryninja.typelibrary.TypeLibrary.new(arch, 'libc.so.0')
    typelib.add_platform(binaryninja.Platform['nanomips'])
    typelib.add_alternate_name('libc.so')

    # default typedefs
    typelib.add_named_type('int8_t', Type.int(1, True))
    typelib.add_named_type('int16_t', Type.int(2, True))
    typelib.add_named_type('int32_t', Type.int(4, True))
    typelib.add_named_type('uint8_t', Type.int(1, False))
    typelib.add_named_type('uint16_t', Type.int(2, False))
    typelib.add_named_type('uint32_t', Type.int(4, False))
    typelib.add_named_type('schar_t', convert(arch, 'int8_t'))
    # TODO: make these platform configuarable
    typelib.add_named_type('size_t', convert(arch, 'unsigned int'))
    typelib.add_named_type('wchar_t', convert(arch, 'unsigned int'))
    typelib.add_named_type('wint_t', Type.int(4, False))
    typelib.add_named_type('wctype_t', convert(arch, 'unsigned long int'))

    with StructureBuilder.builder(typelib, 'ldiv_t') as struct_type:
        struct_type.append(Type.int(4), 'quot')
        struct_type.append(Type.int(4), 'rem')

    with StructureBuilder.builder(typelib, 'div_t') as struct_type:
        struct_type.append(Type.int(4), 'quot')
        struct_type.append(Type.int(4), 'rem')

    for line in lines:
        line = line.strip()
        if not line or line.isspace():
            continue
        if line.startswith('//') or line.startswith('/*'):
            continue

        print(f'/* {line} */')
        result = parse_func_prototype(line)
        pprint.pprint(result, indent=4)

        A = convert(arch, result['return_type'])
        B = [(p['name'], convert(arch, p['type'])) for p in result['params']]
        typelib.add_named_object(result['name'], Type.function(A, B))

    typelib.finalize()
    fname = 'libc.so.0.bntl'
    print(fname)
    typelib.write_to_file(fname)

