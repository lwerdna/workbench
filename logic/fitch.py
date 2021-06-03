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

def Assumption(formula):
    formula = parse(formula)
    return str(formula)

if __name__ == '__main__':
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

