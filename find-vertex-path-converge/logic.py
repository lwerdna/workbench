class ExprNode(object):
    @classmethod
    def true(self):
        return ValNode(True)
    @classmethod
    def false(self):
        return ValNode(False)

    def varnames(self):
        result = set()
        for c in self.children:
            result = result.union(c.varnames())
        return result

    def __repr__(self):
        return str(self)

class AndNode(ExprNode):
    def __init__(self, *children):
        assert all(isinstance(c, ExprNode) for c in children)
        self.children = list(children)

    def evaluate(self, values):
        return all(c.evaluate(values) for c in self.children)

    def prune_vals(self):
        tmp = [c.prune_vals() for c in self.children]

        # if there's a single false being anded, return false
        if [c for c in tmp if c == False]:
            return ExprNode.false()

        # collect children that aren't true
        tmp = [c for c in tmp if c != True]
        match len(tmp):
            case 0:
                return ExprNode.false()
            case 1:
                return tmp[0]
            case _:
                return AndNode(*tmp)

    def omnitrue(self, names):
        return AndNode(*[c.omnitrue(names) for c in self.children])

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)
        return type(other) == AndNode and self.children == other.children

    def __str__(self):
        lines = []
        for c in self.children:
            (l, r) = ('(', ')') if isinstance(c, OrNode) else ('', '')
            lines.append(l + str(c) + r)
        return ''.join(lines)

class OrNode(ExprNode):
    def __init__(self, *children):
        assert all(isinstance(c, ExprNode) for c in children)
        self.children = list(children)

    def evaluate(self, values):
        return any(c.evaluate(values) for c in self.children)

    def prune_vals(self):
        tmp = [c.prune_vals() for c in self.children]

        # if there's a single true being or'd, return true
        if [c for c in tmp if c == True]:
            return ExprNode.true()

        # collect children that aren't false
        tmp = [c for c in tmp if c != False]
        match len(tmp):
            case 0: return ExprNode.false()
            case 1: return tmp[0]
            case _: return OrNode(*tmp)

    def omnitrue(self, names):
        return OrNode(*[c.omnitrue(names) for c in self.children])

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)    
        return type(other) == OrNode and self.children == other.children

    def __str__(self):
        return '+'.join(str(c) for c in self.children)

class NotNode(ExprNode):
    def __init__(self, child):
        assert isinstance(child, ExprNode)
        self.child = child

    def evaluate(self, values):
        return not self.child.evaluate(values)

    def prune_vals(self):
        tmp = self.child.prune_vals()
        if type(tmp) == ValNode:
            return ValNode(not tmp.value)
        return NotNode(tmp)

    def varnames(self):
        return self.child.varnames()

    def omnitrue(self, names):
        if isinstance(self.child, VarNode) and self.child.name in names:
            return ValNode(True)

        return NotNode(self.child.omnitrue(names))

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)    
        return type(other) == NotNode and self.child == other.child

    def __str__(self):
        if isinstance(self.child, VarNode):
            return f'/{self.child}'
        else:
            return f'/({self.child})'

class VarNode(ExprNode):
    def __init__(self, name):
        assert type(name) == str
        self.name = name

    def varnames(self):
        return {self.name}

    def prune_vals(self):
        return self.clone()

    def evaluate(self, values):
        return values[self.name]

    def omnitrue(self, names):
        if self.name in names:
            return ValNode(True)
        else:
            return self.clone()

    def clone(self):
        return VarNode(self.name)

    def __eq__(self, other):
        if type(other) == str:
            other = parse(other)    
        return type(other) == VarNode and self.name == other.name

    def __str__(self):
        return self.name

class ValNode(ExprNode):
    def __init__(self, value):
        assert type(value) == bool
        self.value = value

    def evaluate(self, values):
        return self.value

    def prune_vals(self):
        return self.clone()

    def omnitrue(self, names):
        return self.clone()

    def clone(self):
        return ValNode(self.value)

    def __eq__(self, other):
        if type(other) == bool:
            other = ValNode(other)
        elif type(other) == str:
            other = parse(other)

        return type(other) == ValNode and self.value == other.value

    def __str__(self):
        return {True:'T', False:'F'}[self.value]

