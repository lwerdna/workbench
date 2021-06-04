#!/usr/bin/env python

from formulas.parser import *

class ProofTreeNode(object):
    def __init__(self):
        self.new_prop = None
        self.children = []

    def deduce(self):
        pass

    def str_tree(self, depth=0):
        components = []
        components.append('  '*depth + str(self))
        components.extend([c.str_tree(depth+1) for c in self.children])
        return '\n'.join(components)

    def __str__(self):
        return type(self).__name__ + ': ' + str(self.deduce())

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

class Assumption(ProofTreeNode):
    def __init__(self, formula:str):
        super().__init__()
        self.new_prop = parse(formula)

    #
    # ---
    #  A
    def deduce(self):
        return self.new_prop

if __name__ == '__main__':
    # http://logic.stanford.edu/intrologic/exercises/exercise_04_01.html
    # given p, q, (p^q -> r) prove r
    tree = \
        ImplicationElimination(
            Assumption('(P^Q)->R'),
            AndIntroduction(
                Assumption('P'),
                Assumption('Q')
            ),
        )
    print(tree.str_tree())
    assert str(tree.deduce()) == 'R'

    print('--------')

    # http://logic.stanford.edu/intrologic/exercises/exercise_04_02.html
    # given (p ^ q) prove (q v r)
    tree = \
        OrIntroduction(
            AndElimination(
                Assumption('(P^Q)'),
                'right'
            ),
            'R'
        )
    print(tree.str_tree())
    assert str(tree.deduce()) == '(Q v R)'

#    # http://logic.stanford.edu/intrologic/exercises/exercise_04_03.html
#    # Given p ⇒ q and q ⇔ r, use the Fitch system to prove p ⇒ r
#    proof = \
#        Assumption('P')
#
#            Assumption('P -> Q')
#                Assumption('P')
#            BiImplicationElimination( # Q -> R
#                Assumption('Q <-> R')
#            )
