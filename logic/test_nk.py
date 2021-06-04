#!/usr/bin/env python

from NK import *

# from Takahashi's "A Primer on Proofs and Types"
# (A&B)|(A&C) => A&(B|C)

tree = \
    ImplicationIntroduction( # (A&B)|(A&C) -> A&(B|C)
	    OrElimination( # A&(B|C)
	        Assumption('(A&B)|(A&C)', 'a3'),
	        ImplicationIntroduction( # A&B -> A&(B|C)
	            AndIntroduction( # A&(B|C)
	                AndElimination( # A
	                    Assumption('A&B', label='a1')
	                ),
	                OrIntroduction( # B|C
	                    AndElimination( # B
	                        Assumption('A&B', label='a1'),
	                        'right'
	                    ),
	                    'C'
	                )
	            ),
	            discharge=['a1']
	        ),
	        ImplicationIntroduction(
	            AndIntroduction( # A&C -> A&(B|C)
	                AndElimination( # A
	                    Assumption('A&C', label='a2')
	                ),
	                OrIntroduction( # B|C
	                    AndElimination( # C
	                        Assumption('A&C', label='a2'),
	                        'right'
	                    ),
	                    'B'
	                )
	            ),
	            discharge=['a2']
	        )
	    ),
	    discharge=['a3']
    )
print(tree.str_tree())
assert str(tree.deduce()) == '((A & B) => (A & (B | C)))'
