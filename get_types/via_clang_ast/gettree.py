#!/usr/bin/env python

import os, re, sys
from subprocess import Popen, PIPE

RED = '\x1B[31m'
GREEN = '\x1B[32m'
NORMAL = '\x1B[0m'

def shellout(cmd):
    process = Popen(cmd, stdout=PIPE, stderr=PIPE)
    (stdout, stderr) = process.communicate()
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    process.wait()
    return (stdout, stderr)

# return a number {0,1,2,...} of how "deep" a line returned from -ast-dump is
# the TranslationUnitDecl is depth 0
# anything with |- or `- is >0
def get_depth(line):
    idx = line.find('-')+1
    if idx==-1: return 0
    assert idx % 2 == 0
    return idx // 2

class ClangNode(object):
    def __init__(self, kind, name=None, children=None):
        self.kind = kind
        self.name = name
        self.children = children or []
        self.value = 0 # used in ConstantArrayType
        self.ntr = None # used in FieldDecl

    def tostr(self, depth=0):
        result = '%s%s' % ('  '*depth, self.kind)
        if self.name:
            result += ' name:"%s"' % self.name
        if self.value:
            result += ' value:%d' % self.value
        if self.ntr:
            result += ' ntr:"%s"' % self.ntr
        result += "\n"
        for c in self.children:
            result += c.tostr(depth+1)
        return result

class LineNode(object):
    def __init__(self, line, depth):
        self.children = []
        self.line = self.trim(line)
        self.depth = depth

    def trim(self, line):
        # remove hierarchy chars
        line = line.strip()
        line = line[line.find('-')+1:]

        while True:
            m = re.search(r' 0x[a-f0-9]{8,}', line)
            if m:
                line = line.replace(m.group(0), '')
                continue

            m = re.search(r' <.*>', line)
            if m:
                line = line.replace(m.group(0), '')
                continue

            m = re.search(r' line:\d+:\d+', line)
            if m:
                line = line.replace(m.group(0), '')
                continue

            m = re.search(r' col:\d+', line)
            if m:
                line = line.replace(m.group(0), '')
                continue

            break

        return line

    def toClangNode(self):
        m = re.match(r"^TypedefDecl (.*) '(.*)'$", self.line)
        if m:
            assert len(self.children) == 1
            node = ClangNode('TypedefDecl')
            node.name = m.group(1)
            node.name = node.name.replace('implicit ', '')
            node.children = [self.children[0].toClangNode()]
            return node

        m = re.match(r"^PointerType '(.*)'$", self.line)
        if m:
            assert len(self.children) == 1
            node = ClangNode('PointerType')
            node.children.append(self.children[0].toClangNode())
            return node

        m = re.match(r"^ConstantArrayType '(.*)' (\d+)$", self.line)
        if m:
            assert len(self.children) == 1
            node = ClangNode('ConstantArrayType')
            node.value = int(m.group(2)) # number of elements
            node.children.append(self.children[0].toClangNode())
            return node

        m = re.match(r"^RecordDecl struct (.*) definition$", self.line)
        if m:
            assert len(self.children) > 0
            node = ClangNode('RecordDecl')
            node.name = m.group(1)
            node.children = [n.toClangNode() for n in self.children]
            return node

        m = re.match(r"^FieldDecl (.*) '(.*)'$", self.line)
        if m:
            assert len(self.children) == 0
            node = ClangNode('FieldDecl')
            node.name = m.group(1)
            node.ntr = m.group(2)
            return node

        m = re.match(r"^RecordType ((.*) )?'(.*)'$", self.line)
        if m:
            assert len(self.children) > 0
            node = ClangNode('RecordType')
            if m.group(1):
                node.name = m.group(1)
            node.children = [n.toClangNode() for n in self.children]
            return node

        m = re.match(r"^Record '(.*)'$", self.line)
        if m:
            assert len(self.children) == 0
            node = ClangNode('Record')
            node.name = m.group(1)
            return node

        m = re.match(r"^BuiltinType '(.*)'$", self.line)
        if m:
            assert len(self.children) == 0
            node = ClangNode('BuiltinType')
            node.ntr = m.group(1)
            return node

        m = re.match(r"^ConstantExpr '.*'$", self.line)
        if m:
            node = ClangNode('ConstantExpr')
            node.children = [n.toClangNode() for n in self.children]
            return node

        m = re.match(r"^IntegerLiteral '(.*)' (\d+)$", self.line)
        if m:
            node = ClangNode('ConstantExpr')
            node.value = int(m.group(2))
            node.children = [n.toClangNode() for n in self.children]
            return node

        m = re.match(r"^EnumDecl$", self.line)
        if m:
            assert len(self.children) > 0
            node = ClangNode('EnumDecl')
            node.children = [n.toClangNode() for n in self.children]
            return node

        m = re.match(r"^EnumConstantDecl (.*) '(.*)'$", self.line)
        if m:
            node = ClangNode('EnumConstantDecl')
            node.name = m.group(1)
            node.children = [n.toClangNode() for n in self.children]
            return node

        print(repr(self.line))
        raise Exception('cannot parse "%s"' % self.line)

    def __str__(self):
        result = '  '*self.depth + self.line + '\n'
        for c in self.children:
            result += str(c)
        return result

def parse_to_line_nodes(fpath):
    cmd = ['clang', '-Xclang', '-ast-dump', '-fsyntax-only', fpath]
    (stdout, stderr) = shellout(cmd)

    lines = stdout.split('\n')
    assert lines[0].startswith('TranslationUnitDecl')
    while not lines[-1]:
        lines.pop()

    # translate indent-specified hierarchy into object hierarchy
    stack = [LineNode(lines[0], 0)]
    for line in lines[1:]:
        newdepth = get_depth(line)
        
        # seek parent
        while newdepth <= stack[-1].depth:
            stack.pop()
        # add child
        newnode = LineNode(line, newdepth)
        stack[-1].children.append(newnode)
        # child becomes new top of stack
        stack.append(newnode)

    root = stack[0]
    return root.children

def parse_to_clang_nodes(fpath):
    lnodes = parse_to_line_nodes(fpath)
    return [lnode.toClangNode() for lnode in lnodes]

def parse(fpath):
    return parse_to_clang_nodes(fpath)

if __name__ == '__main__':
    lnodes = parse_to_line_nodes(sys.argv[1])

    for (i, ln) in enumerate(lnodes):
        print('LineNode %d:' % i)
        print(ln)

    print('--------')

    cnodes = [lnode.toClangNode() for lnode in lnodes]

    for (i, cn) in enumerate(cnodes):
        print('ClangNode %d:' % i)
        print(cn.tostr())
