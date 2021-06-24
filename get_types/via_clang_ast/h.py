#!/usr/bin/env python

# parse the ClangNodes back to a header, an identity transformation

import os, sys, re
import gettree

def declaration(cn, depth=0):
    indent = '\t'*depth

    result = ''

    if cn.kind == 'TypedefDecl':
        return 'typedef %s %s;' % (declaration(cn.children[0], depth+1), cn.name)

    if cn.kind == 'RecordType':
        return declaration(cn.children[0], depth+1)

    if cn.kind == 'Record':
        return cn.name

    if cn.kind == 'BuiltinType':
        return cn.ntr

    if cn.kind == 'PointerType':
        tmp = declaration(cn.children[0])
        return '%s *' % tmp

    if cn.kind == 'ConstantArrayType':
        tmp = declaration(cn.children[0])
        return '%s[%d]' % (tmp, cn.length)

    if cn.kind == 'RecordDecl':
        result += '%sstruct %s\n' % (indent, cn.name)
        result += '%s{\n' % indent
        for child in cn.children:
            result += declaration(child, depth+1) + '\n'
        result += '%s};' % indent
        return result

    if cn.kind == 'FieldDecl':
        result += '%s%s %s;' % (indent, cn.ntr, cn.name)
        return result

    raise Exception('cannot handle kind %s' % cn.kind)

if __name__ == '__main__':
    cnodes = gettree.parse(sys.argv[1])

    for (i, cn) in enumerate(cnodes):
        #print('clangnode %d:' % i)
        #print(cn.tostr())
        print(declaration(cn))
