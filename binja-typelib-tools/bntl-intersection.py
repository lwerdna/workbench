#!/usr/bin/env python

# compute the intersection (the shared types) between two typelibs

import os, sys, re, random
import binaryninja
from binaryninja.enums import *
from binaryninja import typelibrary

def types_equal(A, B):
    if A.type_class != B.type_class:
        return false
    if A.width != B.width:
        return false

    match A.type_class:
        case TypeClass.IntegerTypeClass:
            #return signed == A.signed
            assert False
        case TypeClass.StructureTypeClass:
            #return (*struct) == (*A.struct)
            assert False
        case TypeClass.NamedTypeReferenceClass:
            #return namedTypeRef->GetName() == A.namedTypeRef->GetName()
            assert False
        case TypeClass.EnumerationTypeClass:
            #return (*enum) == (*A.enum)
            assert False
        case TypeClass.PointerTypeClass:
            #if namedTypeRef && A.namedTypeRef:
            #{
            #    if namedTypeRef->GetName() != A.namedTypeRef->GetName():
            #        return false
            #    if offset != A.offset:
            #        return false
            #}
            #else if namedTypeRef || A.namedTypeRef:
            #    return false
            #if struct && A.struct:
            #{
            #    if (*struct) != (*A.struct):
            #        return false
            #    if offset != A.offset:
            #        return false
            #}
            #else if struct || A.struct:
            #    return false
            #if childA.GetConfidence() != A.childA.GetConfidence():
            #    return false
            #return (*childType) == (*A.childType)
            assert False
        case TypeClass.ArrayTypeClass:
            #if childA.GetConfidence() != A.childA.GetConfidence():
            #    return false
            #if (*childType) != (*A.childType):
            #    return false
            #return elements == A.elements
            assert False
        case TypeClass.FunctionTypeClass:
            if A.confidence != B.confidence:
                reason = f'\tconfidence mismatch:\n\t{A.confidence} vs.\n\t{B.confidence}'
                return False
            #if A.calling_convention != B.calling_convention:
            #    print(f'calling_convention mismatch: {A.calling_convention} vs. {B.calling_convention}')
            #    return False
            if A.parameters != B.parameters:
                reason = f'\tparameters mismatch:\n\t{A.parameters} vs.\n\t{B.parameters}'
                return (False, reason)
            if A.can_return != B.can_return:
                reason = f'\tcan_return mismatch:\n\t{A.can_return} vs.\n\t{B.can_return}'
                return (False, reason)
            if A.system_call_number != B.system_call_number:
                reason = f'\tsystem_call_number mismatch:\n\t{A.system_call_number} vs.\n\t{B.system_call_number}'
                return (False, reason)
            if A.stack_adjustment != B.stack_adjustment:
                reason = f'\tstack_adjustment mismatch:\n\t{A.stack_adjustment} vs.\n\t{B.stack_adjustment}'
                return (False, reason)
            return (True, '')
        case _:
            assert False

if __name__ == '__main__':
    binaryninja._init_plugins()

    if len(sys.argv) <= 2:
        raise Exception('supply at least two typelib files')

    fpath0, fpath1 = sys.argv[1], sys.argv[2]

    tl0 = typelibrary.TypeLibrary.load_from_file(fpath0)
    tl1 = typelibrary.TypeLibrary.load_from_file(fpath1)

#    print('           name: %s' % tl.name)
#    print('           arch: %s' % tl.arch)
#    print('           guid: %s' % tl.guid)
#    print('dependency_name: %s' % tl.dependency_name)
#    print('alternate_names: %s' % tl.alternate_names)
#    print(' platform_names: %s' % tl.platform_names)
#    print('')

    A = set(tl0.named_objects)
    B = set(tl1.named_objects)
    print(f'{len(A)} named objects in A')
    print(f'{len(B)} named objects in B')
    print(f'{len(A-B)} named objects in A ONLY')
    print(f'{len(B-A)} named objects in B ONLY')
    print(f'{len(A.intersection(B))} named objects common in A, B')

    all_names = set(list(tl0.named_objects.keys()) + list(tl1.named_objects.keys()))
    print(f'{len(all_names)} named objects in total (counting common names once)')
    
    common_named_objects = 0

    print('  named_objects: %d' % len(tl0.named_objects))
    for name in sorted(all_names):
        name = '__fxstat'
        breakpoint()

        if not name in tl0.named_objects:
            print(f'B only {name}')
            continue

        if not name in tl1.named_objects:
            print(f'A only {name}')
            continue

        type0 = tl0.named_objects[name]
        type1 = tl1.named_objects[name]

        (result, reason) = types_equal(type0, type1)
        if result:
            print(f'A == B {name}')
            common_named_objects += 1
        else:
            print(f'A != B {name}')
            print(reason)


    print(f'intersection of agreement: {common_named_objects}')

