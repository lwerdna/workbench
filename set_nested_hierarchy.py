#!/usr/bin/env python3

# insertion of sets into a nested/inclusion/containment hierarchy
# see: https://en.wikipedia.org/wiki/Nested_set

class SNode():
    def __init__(self, set_=set(), children=[]):
        self.set_ = set_
        self.children = children

    def insert(self, new_set):
        # CASE0: incoming set is the superset of one or more children
        subset_idxs = []
        for (i,child) in enumerate(self.children):
            if new_set > child.set_:
                subset_idxs.append(i)

        if subset_idxs:
            new_children = []
            for idx in sorted(subset_idxs, reverse=True):
                new_children.append(self.children.pop(idx))
            self.children.append(SNode(new_set, new_children))
            return self

        # CASE1: incoming set is the subset of a child
        superset_idxs = []
        for (i,child) in enumerate(self.children):
            if new_set < child.set_:
                superset_idxs.append(i)
        assert len(superset_idxs) in [0,1]

        if superset_idxs:
            self.children[superset_idxs[0]] = self.children[superset_idxs[0]].insert(new_set)
            return self

        # CASE2: incoming set is simply a new sibling
        self.children.append(SNode(new_set, []))
        return self

    def check(self):
        if self.set_:
            for child in self.children:
                assert self.set_ > child.set_

        for child in self.children:
            child.check()

    def str_helper(self, depth):
        result = []
        if self.set_:
            result.append('    '*depth + str(self.set_))
        for child in self.children:
            result.extend(child.str_helper(depth+1))
        return result

    def __str__(self):
        lines = self.str_helper(0)
        return '\n'.join(lines)

a = set([1,2,3,4,5,6,7,8,9,10])
b = set([4,5])
c = set([6,7])
d = set([8])
e = set([3,4,5,6,7])
f = set([4,5,6])
g = set([7,8,9,10])
h = set([1,2])
i = set([9,10])
j = set([5])

snode = SNode()
for foo in [a,b,c,d,e,f,g,h,i,j]:
    snode.insert(foo)
snode.check()
print(snode)
