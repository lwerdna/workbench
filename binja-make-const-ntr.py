#!/usr/bin/env python

# How can you create a named type reference that is const?

# They exist in the wild, this is from libpthread_x86_64.so.0.bntl that ships with Binary Ninja:
#
# (Pdb) foo
# <named_type_reference: union pthread_attr_t const>
# (Pdb) foo.const
# BoolWithConfidence(value=True, confidence=255)
# (Pdb) type(foo)
# <class 'binaryninja.types.NamedTypeReferenceType'>
#
# Which is the parameter to __pthread_get_minstack() which has type within Binary Ninja:
#
# <type: size_t (union pthread_attr_t const* attr)>

import os, sys, re, random, json

import binaryninja
from binaryninja import typelibrary
from binaryninja.types import Type, TypeBuilder, QualifiedName
from binaryninja.enums import NamedTypeReferenceClass

# -----------------------------------------------------------------------------
# attempt #1: use the static named_type_reference() function in Type,
#             set const afterwards
# -----------------------------------------------------------------------------

foo = Type.named_type_reference(
        NamedTypeReferenceClass.UnionNamedTypeClass, # type_class
        'pthread_attr_t', # name
        'libc.so.6:["pthread_attr_t"]', # type_id
        1, # alignment
        56 # width
    )
print(repr(foo))

if foo.const:
    print("SUCCEEDED")
else:
    try:
        foo.const = True
        print("SUCCEEDED")
    except AttributeError as e:
        print("FAILED")

# -----------------------------------------------------------------------------
# attempt #2: use the named_type_reference() function in TypeBuilder
# -----------------------------------------------------------------------------
builder = TypeBuilder.named_type_reference(
        NamedTypeReferenceClass.UnionNamedTypeClass, # type_class
        QualifiedName('pthread_attr_t'), # name
        'libc.so.6:["pthread_attr_t"]', # type_id
        1, # alignment
        56 # width
    )

builder.const = True
assert builder.const == True

foo = Type.named_type(builder)
if foo.const:
    print("SUCCEEDED")
else:
    try:
        foo.const = True
        print("SUCCEEDED")
    except AttributeError as e:
        print("FAILED")

# -----------------------------------------------------------------------------
# attempt #3: ask the core to set const in the builder
# -----------------------------------------------------------------------------

builder = TypeBuilder.named_type_reference(
        NamedTypeReferenceClass.UnionNamedTypeClass, # type_class
        QualifiedName('pthread_attr_t'), # name
        'libc.so.6:["pthread_attr_t"]', # type_id
        1, # alignment
        56 # width
    )

assert builder.const == False
binaryninja.core.BNTypeBuilderSetConst(builder._handle, binaryninja.types.BoolWithConfidence(True, binaryninja.core.max_confidence).get_core_struct(True))
assert builder.const == True

foo = Type.named_type(builder)
if foo.const:
    print("SUCCEEDED")
else:
    try:
        foo.const = True
        print("SUCCEEDED")
    except AttributeError as e:
        print("FAILED")

