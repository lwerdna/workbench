# intended to be a "grab bag" of inference rules and tools that different
# logic systems can select from

from formulas.parser import *

class ProofTreeNode(object):
    def __init__(self):
        self.new_prop = None # used in or introduction and assumptions
        self.label = None # to refer to during discharging
        self.discharge_label = None
        self.children = []

    def deduce(self):
        pass

    def str_tree(self, depth=0):
        components = []
        components.append('  '*depth + str(self))
        components.extend([c.str_tree(depth+1) for c in self.children])
        return '\n'.join(components)

    def find_assumptions(self, label=None):
        result = []

        if type(self) == Assumption and (not label or self.label == label):
            result = [self]
        else:
            for c in self.children:
                result.extend(c.find_assumptions(label))

        return result

    def check_deduction(self, goal:str):
        return self.deduce() == parse(goal)

    def check_proof(self, goal:str):
        if not self.check_deduction(goal):
            return False

        return all(a.state == 'discharged' for a in self.find_assumptions())

    def discharge(self, optional=False):
        if not self.discharge_label:
            if optional:
                return
            else:
                assert self.discharge_label, "discharge() called when no discharge label set"

        tree_nodes = self.find_assumptions(self.discharge_label)
        assert tree_nodes != []
        assert all(e == tree_nodes[0] for e in tree_nodes), 'different nodes labelled %s' % label
        for tn in tree_nodes:
            tn.state = 'discharged'
        return tree_nodes[0]

    def __str__(self):
        return type(self).__name__ + ': ' + str(self.deduce())


class ImplicationIntroduction(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, discharge=None):
        super().__init__()
        self.children = [a]
        self.discharge_label = discharge

    # [A]
    #  .
    #  .
    #  B
    # ------
    # A -> B
    def deduce(self):
        consequent = self.children[0].deduce()
        antecedent = self.discharge().deduce()
        return Implication(antecedent, consequent)

    def __str__(self):
        return '%s: %s discharges: %s' % (type(self).__name__, str(self.deduce()),
            self.discharge_label)


class ImplicationElimination(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, b:ProofTreeNode):
        super().__init__()
        self.children = [a,b]

    # A->B, A
    # -------
    #    B
    def deduce(self):
        implication = self.children[0].deduce()
        assert type(implication) == Implication

        antecedent = self.children[1].deduce()
        assert implication.left == antecedent

        return implication.right

class BiImplicationElimination(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, which='left'):
        super().__init__()
        self.children = [a]
        assert which in ['left', 'right']
        self.which = which

    # A<->B
    # -----
    #  A->B
    def deduce(self):
        biimplication = self.children[0].deduce()
        assert type(biimplication) == BiImplication

        if self.which == 'left':
            return Implication(biimplication.left, biimplication.right)
        else:
            return Implication(biimplication.right, biimplication.left)

class AndIntroduction(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, b:ProofTreeNode):
        super().__init__()
        self.children = [a,b]

    def deduce(self):
        return Conjunction(self.children[0].deduce(), self.children[1].deduce())

class AndElimination(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, which='left'):
        super().__init__()
        self.children = [a]
        assert which in ['left', 'right']
        self.which = which

    # A^B
    # ---
    #  A
    def deduce(self):
        conjunction = self.children[0].deduce()
        assert type(conjunction) == Conjunction

        if self.which == 'left':
            return conjunction.left
        else:
            return conjunction.right

class OrIntroduction(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, new_prop:str):
        super().__init__()
        self.children = [a]
        self.new_prop = parse(new_prop)

    # A, B
    # ----
    # AvB
    def deduce(self):
        return Disjunction(self.children[0].deduce(), self.new_prop)

class OrElimination(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, b:ProofTreeNode, c:ProofTreeNode, discharge=None):
        super().__init__()
        self.children = [a, b, c]
        self.discharge_label = discharge

    # A v B, A->C, B->C
    # -----------------
    #        C
    def deduce(self):
        conjunction:ASTNode = self.children[0].deduce()
        implication1:ASTNode = self.children[1].deduce()
        implication2:ASTNode = self.children[2].deduce()

        assert type(implication1) == Implication
        assert implication1.left == conjunction.left

        assert type(implication2) == Implication
        assert implication2.left == conjunction.right

        assert implication1.right == implication2.right

        # discharge assumptions
        self.discharge(optional=True)

        return implication1.right

    def __str__(self):
        result = '%s: %s' % (type(self).__name__, str(self.deduce()))
        if self.discharge_label:
            result += ' discharges: %s' % self.discharge_label
        return result

class NegationIntroduction(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, discharge=None):
        super().__init__()
        self.children = [a]
        self.discharge_label = discharge

    # [A]      note: this only _ADDS_ negation
    #  .       classic absurdity is needed to remove negation
    #  .       ~~A == A is not taken for granted
    #  .
    #  _
    # ------
    #  ~A
    def deduce(self):
        assert type(self.children[0].deduce()) == Contradiction
        astnode = self.discharge().deduce()
        assert type(astnode) != Negation
        return Negation(astnode)

class NegationElimination(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, b:ProofTreeNode):
        super().__init__()
        self.children = [a,b]

    # A & ~A
    # ------
    #   _
    def deduce(self):
        a:ASTNode = self.children[0].deduce()
        b:ASTNode = self.children[1].deduce()
        assert a == Negation(b) or Negation(a) == b
        return Contradiction()

class ClassicalAbsurdity(ProofTreeNode):
    def __init__(self, a:ProofTreeNode, discharge=None):
        super().__init__()
        self.children = [a]
        self.discharge_label = discharge

    # [A]      note: only _REMOVES_ negation
    #  .       ~~A == A is not taken for granted
    #  .
    #  .
    #  _
    # ---
    # ~A
    def deduce(self):
        assert type(self.children[0].deduce()) == Contradiction
        astnode = self.discharge().deduce()
        assert type(astnode) == Negation
        return astnode.left

class Assumption(ProofTreeNode):
    def __init__(self, formula:str, label:str=None):
        super().__init__()
        self.new_prop = parse(formula)
        self.label = label
        self.state = 'active' # or 'discharged'

    #
    # ---
    #  A
    def deduce(self):
        return self.new_prop

    def discharge(self):
        self.state = 'discharged'

    def __str__(self):
        return '%s: [%s] "%s" %s' % (type(self).__name__, self.deduce(), self.label or '', self.state)

    def __eq__(self, other):
        return type(self)==type(other) and self.new_prop==other.new_prop and self.state == other.state
