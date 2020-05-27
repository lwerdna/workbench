#!/usr/bin/env python

import sys
import itertools

varstr = 'ABCDEFGHI'

print('\n'.join(['(declare-const %s Bool)'%x for x in varstr]))

print('''
(define-fun no_attacks () Bool
  (and
    (or (not A) (and (not B) (not C) (not D) (not G)))
    (or (not B) (and (not A) (not C) (not E) (not H)))
    (or (not C) (and (not A) (not B) (not F) (not I)))
    (or (not D) (and (not A) (not E) (not F) (not G)))
    (or (not E) (and (not B) (not D) (not F) (not H)))
    (or (not F) (and (not D) (not E) (not C) (not I)))
    (or (not G) (and (not A) (not D) (not H) (not I)))
    (or (not H) (and (not G) (not B) (not E) (not I)))
    (or (not I) (and (not G) (not H) (not C) (not F)))
  )
)
''')

print('(define-fun exactly_three () Bool')
print('  (or')
for chosen in itertools.combinations('ABCDEFGHI', 3):
	unchosen = [x for x in 'ABCDEFGHI' if not x in chosen]
	print('    (and '+' '.join(list(chosen) + ['(not %s)'%x for x in unchosen])+')')
print('  )')
print(')')

print('''
(define-fun conjecture () Bool
  (and no_attacks exactly_three)
)

(assert conjecture)
(check-sat)
(get-model)
''')

