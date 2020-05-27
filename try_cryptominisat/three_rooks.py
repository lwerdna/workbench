#!/usr/bin/env python

import sys
import itertools
from cms5_wrapper import solve_english

# Imagine a 3x3 chessboard with these marked squares:
#
# A B C
# D E F
# G H I
#
# How can rooks be placed so they don't attack each other?
#
# model:
# let variable A be true iff a rook is at square A
# assert true
# A -> /B /C /D /G because of how the rook moves
# B -> /A /C /E /H
# ... etc.
# assert true that at most three of A,B,C,D,E,F,G,H,I are true

proposition = ''

rook_propositions = []
rook_propositions.append('(~A | ~B & ~C & ~D & ~G)')
rook_propositions.append('(~B | ~A & ~C & ~E & ~H)')
rook_propositions.append('(~C | ~A & ~B & ~F & ~I)')
rook_propositions.append('(~D | ~A & ~E & ~F & ~G)')
rook_propositions.append('(~E | ~B & ~D & ~F & ~H)')
rook_propositions.append('(~F | ~D & ~E & ~C & ~I)')
rook_propositions.append('(~G | ~A & ~D & ~H & ~I)')
rook_propositions.append('(~H | ~G & ~B & ~E & ~I)')
rook_propositions.append('(~I | ~G & ~H & ~C & ~F)')

# A & B & C & ~D & ~E & ~F & ~G & ~H & ~I
# A & B & D & ~C & ~E & ~F & ~G & ~H & ~I
# ...
exactly_three_propositions = []
for chosen in itertools.combinations('ABCDEFGHI', 3):
	unchosen = [x for x in 'ABCDEFGHI' if not x in chosen]
	prop = '('+' & '.join(list(chosen) + ['~'+x for x in unchosen])+')'
	exactly_three_propositions.append(prop)
	
prop = ' & '.join(rook_propositions) + ' & (' + '|'.join(exactly_three_propositions) + ')'
print(prop)

for solution in solve_english(prop):
	print('solution: ', solution)

