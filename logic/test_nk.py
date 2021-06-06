#!/usr/bin/env python

from NK import *

# from Takahashi's "A Primer on Proofs and Types"
# (A&B)|(A&C) => A&(B|C)

# note our OrElimination is a bit more stringent than the paper's
# ours takes implications as input so there's implication introduction wrapping
# the two inputs into OrElimination and a1 and a2 are discharged there

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
	            discharge='a1'
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
	            discharge='a2'
	        )
	    ),
	    discharge='a3'
    )
print(tree.str_tree())
assert tree.check_proof('((A & B)|(A & C)) => (A & (B | C))')

print('--------')

# law of excluded middle
tree = \
    ClassicalAbsurdity( # A | ~A
		NegationElimination( # _
		    OrIntroduction( # A | ~A
		        NegationIntroduction( # ~A
		            NegationElimination( # _
		            Assumption('~(A|~A)', label='a2'),
		                OrIntroduction( # A | ~A
		                    Assumption('A', label='a1'),
		                    '~A'
		                    )
		            ),
		            discharge='a1'
		        ),
		        'A'
		    ),
		    Assumption('~(A|~A)', label='a2')
		),
		discharge='a2'
	)
print(tree.str_tree())
assert tree.check_proof('A|~A')
