#!/usr/bin/env python

import os, sys, re, pprint

from subprocess import Popen, PIPE

def shellout(cmd):
    process = Popen(cmd, stdout=PIPE, stderr=PIPE)
    (stdout, stderr) = process.communicate()
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    #print('stdout: -%s-' % stdout)
    #print('stderr: -%s-' % stderr)
    process.wait()
    return (stdout, stderr)

def dot_label_escape(string):
    string = string.replace('"', '\\"')
    return string

class DNode():
    def __init__(self, lines):
        m = re.match(r'^(0x[0-9A-Fa-f]+): ( *)(DW_TAG_.*)$', lines[0])
        assert m

        #self.lines = lines
        self.offset = int(m.group(1), 16)
        self.depth = len(m.group(2)) // 2
        self.tag = m.group(3)

        self.attributes = {}
        for line in lines[1:]:
            m = re.match(r'^\s*(DW_AT_\w+)\s+(.*)$', line)
            if not m:
                continue

            left = m.group(1)
            right = m.group(2)

            # replace (0x000001c7 "__u64") with 0x1c7
            if m := re.match(r'^\((0x[0-9A-Fa-f]+)\s+"[\w\s\[\]\*]+"\)$', right):
                right = int(m.group(1), 16)
            # replace (0x04) with 0x04
            elif m := re.match(r'^\((0x[0-9A-Fa-f]+)\)$', right):
                right = int(m.group(1), 16)
            # replace '("foo")' with 'foo'
            elif m := re.match(r'^\("([\w\s]+)"\)$', right):
                right = m.group(1)

            self.attributes[left] = right

        self.children = []
        self.offset_to_node = {}

    def deref_attributes(self, lookup):
        if type(self.type) == int:
            self.attributes['DW_AT_type'] = lookup[self.type]

    def __str__(self):
        return '0x%X: %s' % (self.offset, self.tag)

    #----------------------------------------------------------
    # accessors for common attributes
    #----------------------------------------------------------
    @property
    def name(self):
        return self.attributes.get('DW_AT_name', None)

    @property
    def type(self):
        return self.attributes.get('DW_AT_type', None)

    @property
    def byte_size(self):
        if sz := self.attributes.get('DW_AT_byte_size', None):
            return sz

        # if we're a typedef or a restrict or a const we must look deeper...
        assert self.type
        return self.type.byte_size

    @property
    def encoding(self):
        return self.attributes.get('DW_AT_encoding', None)

# return node and all nodes reachable from this node
def reachable(root):
    result = set()

    queue = [root]
    while queue:
        current = queue.pop()
        if current in result:
            continue

        result.add(current)

        for child in current.children:
            queue.append(child)

        if current.type:
            queue.append(current.type)

    return result

def parse(output, NodeClass):
    lines = output.splitlines()

    nodes = []
    (start, end) = (None, None)
    for (i, line) in enumerate(lines):
        if m := re.match(r'^0x[0-9A-Fa-f]+: +DW_TAG_.*$', line):
            start = i 
        elif re.match(r'^\s*$', line):
            if start != None:
                end = i
                nodes.append(NodeClass(lines[start:end]))
                (start, end) = (None, None)
        else:
            pass

    # make tree structure
    stack = []
    for node in nodes:
        if node == None:
            breakpoint()
        # search "up" for possible parent
        while stack and not (stack[-1].depth == node.depth-1):
            stack.pop()

        if stack:
            stack[-1].children.append(node)

        stack.append(node)

    #return [n for n in nodes if n.depth == 0]
    return nodes

# call dwarfdump, return graph of DIEs
def dwarfdump(args, NodeClass):
    (stdout, stderr) = shellout(['dwarfdump'] + args)
    nodes = parse(stdout, NodeClass)

    offset_to_node = {n.offset:n for n in nodes}
    for node in nodes:
        node.deref_attributes(offset_to_node)

    return nodes

# return a requested function (subprogram) DIE
def dwarfdump_function(fpath, func_name, NodeClass):
    nodes = dwarfdump([fpath], NodeClass)

    matches = [n for n in nodes if n.tag == 'DW_TAG_subprogram' and n.name == func_name]
    assert matches

    # if multiple matches found, return the one with the most arguments
    if len(matches) > 0:
        matches = sorted(matches, key=lambda x: len(x.children), reverse=True)

    result = matches[0]

    # filter unnecessary DIEs
    blacklist = ['DW_TAG_GNU_call_site', 'DW_TAG_lexical_block', 'DW_TAG_variable']
    result.children = [c for c in result.children if not (c.tag in blacklist)]

    return result

# return a requested structure DIE
def dwarfdump_structure(fpath, struct_name, NodeClass):
    nodes = dwarfdump([fpath], NodeClass)
    matches = [n for n in nodes if n.tag == 'DW_TAG_structure_type' and n.name == struct_name]

    # if multiple matches found, return the one with the most children
    # note that empty (no defining) declarations have no children
    if len(matches) > 0:
        matches = sorted(matches, key=lambda x: len(x.children), reverse=True)

    assert matches
    return matches[0]

