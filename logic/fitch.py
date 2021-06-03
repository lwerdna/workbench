#!/usr/bin/env python

from formulas.parser import *

def ImplicationElimination(implication:str, antecedent:str):
    implication = parse(implication)
    antecedent = parse(antecedent)

    assert type(implication) == Implication
    assert implication.left == antecedent

    return str(implication.right)

#def AndIntroduction(formula:str, arg0:str, arg1:str):
#    formula = parse(formula)
#    arg0 = parse(arg0)
#    arg1 = parse(arg1)
#
#    assert type(formula) == Conjunction
#    assert (formula.left == arg0 and formula.right == arg1) or \
#            (formula.left == arg1 and formula.right == arg0)
#
#    return str(formula)

def AndIntroduction(arg0:str, arg1:str):
    arg0 = parse(arg0)
    arg1 = parse(arg1)
    formula = Conjunction(arg0, arg1)
    return str(formula)

def AndElimination(arg0:str, which='left'):
    arg0 = parse(arg0)
    assert type(arg0) == Conjunction

    if which == 'left':
        return str(arg0.left)
    elif which == 'right':
        return str(arg0.right)
    assert False

def OrIntroduction(arg0:str, arg1:str):
    arg0 = parse(arg0)
    arg1 = parse(arg1)
    formula = Disjunction(arg0, arg1)
    return str(formula)

def Assumption(formula):
    formula = parse(formula)
    return str(formula)

if __name__ == '__main__':
    # http://logic.stanford.edu/intrologic/exercises/exercise_04_01.html
    # given p, q, (p^q -> r) prove r
    proof = \
        ImplicationElimination(
            Assumption('(P^Q)->R'),
            AndIntroduction(
                Assumption('P'),
                Assumption('Q')
            ),
        )
    print(proof)
    assert proof == 'R'

    # http://logic.stanford.edu/intrologic/exercises/exercise_04_02.html
    # given (p ^ q) prove (q v r)
    proof = \
        OrIntroduction(
            AndElimination(
                Assumption('(P^Q)'),
                'right'
            ),
            'R'
        )
    print(proof)
    assert proof == '(Q v R)'
