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

    qualifiers = ['const', 'signed', 'unsigned']
    known_types = ['void', 'int', 'char', 'size_t']

    tokens = tokenize(line)

    while tokens[0] in qualifiers + known_types + ['*']:
        result['return_type'].append(tokens.pop(0))

    result['name'] = tokens.pop(0)

    assert tokens[0] == '(', breakpoint()
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

def process_type(arch, tokens):
    smashed = ' '.join(tokens)
    print(f'smashed: {smashed}')
    match smashed:
        case 'void *':
            return Type.pointer(arch, Type.void())
        case 'const void *':
            return Type.pointer(arch, Type.void(), True)
        case 'char':
            return Type.int(1)
        case 'char *':
            return Type.pointer(arch, Type.int(1))
        case 'const char *':
            return Type.pointer(arch, Type.int(1), True)
        case 'int':
            return Type.int(1)
        case 'int *':
            return Type.pointer(arch, Type.int(4))
        case 'size_t':
            return NamedTypeReferenceType.create(named_type_class=NamedTypeReferenceClass.TypedefNamedTypeClass, guid=None, name='size_t')
        case _:
            breakpoint()
            pass

if __name__ == '__main__':
    # read prototypes from header
    lines = [l.strip() for l in open('prototypes.h').readlines()]

    while lines[0].startswith('typedef'):
        lines.pop(0)
    while lines[0].isspace() or lines[0] == '':
        lines.pop(0)

    # prepare binja
    arch = binaryninja.Architecture['mipsel32']
    typelib = binaryninja.typelibrary.TypeLibrary.new(arch, 'libc.so.0')
    typelib.add_platform(binaryninja.Platform['linux-mipsel'])
    typelib.add_alternate_name('libc.so')

    for line in lines:
        line = line.strip()
        if not line or line.isspace():
            continue
        if line.startswith('//') or line.startswith('/*'):
            continue
        if line == 'typedef unsigned int size_t;':
            typelib.add_named_type('size_t', Type.int(4))            
            continue

        print(f'/* {line} */')
        result = parse_func_prototype(line)
        pprint.pprint(result, indent=4)

        A = process_type(arch, result['return_type'])
        B = [(p['name'], process_type(arch, p['type'])) for p in result['params']]
        typelib.add_named_object(result['name'], Type.function(A, B))

    typelib.finalize()
    print('writing test.bntl')
    typelib.write_to_file('test.bntl')

