#!/usr/bin/env python

class hnode():
    def __init__(self, item, children=None):
        self.item = item
        self.children = children
        if self.children == None:
            self.children = []
        self.dummy_root = False

    def apply_sort(self, sort_key=None):
        for c in self.children:
            c.apply_sort(sort_key)

        if sort_key:
            self.children = sorted(self.children, key=lambda n: sort_key(n.item))
        else:
            self.children = sorted(self.children, key=lambda n: n.item)

    def __str_depth__(self, depth):
        result = '  '*depth + str(self.item)
        if self.children:
            result += '\n'
            result += '\n'.join([c.__str_depth__(depth+1) for c in self.children])
        return result

    def __str__(self):
        return self.__str_depth__(0)

# relation(a,b) true iff a is a "parent" of b
def hierarchy_worker(current, item, is_ancestor):
    # is currently inserted item the ancestor of the insertion point?
    if is_ancestor(item, current.item):
        return hnode(item, [current])

    # is the currently inserted item ancestor of insertion point's children?
    offs_nodes = [n for n in current.children if is_ancestor(item, n.item)]
    if len(offs_nodes) > 0:
        current.children = [c for c in current.children if not is_ancestor(item, c.item)]
        current.children.append(hnode(item, offs_nodes))
        return current

    # is the currently inserted item the offspring of one of the insertion point's children?
    for (i,child_node) in enumerate(current.children):
        if is_ancestor(child_node.item, item):
            current.children[i] = hierarchy_worker(child_node, item, is_ancestor)
            return current

    # then the currently inserted item is the offspring of the insertion point
    assert is_ancestor(current.item, item) or current.dummy_root
    current.children.append(hnode(item))
    return current

def hierarchy(items, is_ancestor, sort_func=None):
    root = hnode("root")
    root.dummy_root = True
    for item in items:
        hierarchy_worker(root, item, is_ancestor)

    if sort_func:
        root.apply_sort(sort_func)

    return root



