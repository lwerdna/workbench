; "heavy" solution - many expressions to enforce movement
; - rook on A means no B, C, D, G
; - explicit encoding for "at least three"

; Imagine a 3x3 chessboard:
;
; A B C
; D E F
; G H I
;
; Where can rooks be placed so they don't attack one another?
;
; $ z3 ./three_rooks.smt2

(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)
(declare-const E Bool)
(declare-const F Bool)
(declare-const G Bool)
(declare-const H Bool)
(declare-const I Bool)

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

; generated with:
; for chosen in itertools.combinations('ABCDEFGHI', 3):
;     unchosen = [x for x in 'ABCDEFGHI' if not x in chosen]
;     print('    (and '+' '.join(list(chosen) + ['(not %s)'%x for x in unchosen])+')'
(define-fun exactly_three () Bool
  (or
    (and A B C (not D) (not E) (not F) (not G) (not H) (not I))
    (and A B D (not C) (not E) (not F) (not G) (not H) (not I))
    (and A B E (not C) (not D) (not F) (not G) (not H) (not I))
    (and A B F (not C) (not D) (not E) (not G) (not H) (not I))
    (and A B G (not C) (not D) (not E) (not F) (not H) (not I))
    (and A B H (not C) (not D) (not E) (not F) (not G) (not I))
    (and A B I (not C) (not D) (not E) (not F) (not G) (not H))
    (and A C D (not B) (not E) (not F) (not G) (not H) (not I))
    (and A C E (not B) (not D) (not F) (not G) (not H) (not I))
    (and A C F (not B) (not D) (not E) (not G) (not H) (not I))
    (and A C G (not B) (not D) (not E) (not F) (not H) (not I))
    (and A C H (not B) (not D) (not E) (not F) (not G) (not I))
    (and A C I (not B) (not D) (not E) (not F) (not G) (not H))
    (and A D E (not B) (not C) (not F) (not G) (not H) (not I))
    (and A D F (not B) (not C) (not E) (not G) (not H) (not I))
    (and A D G (not B) (not C) (not E) (not F) (not H) (not I))
    (and A D H (not B) (not C) (not E) (not F) (not G) (not I))
    (and A D I (not B) (not C) (not E) (not F) (not G) (not H))
    (and A E F (not B) (not C) (not D) (not G) (not H) (not I))
    (and A E G (not B) (not C) (not D) (not F) (not H) (not I))
    (and A E H (not B) (not C) (not D) (not F) (not G) (not I))
    (and A E I (not B) (not C) (not D) (not F) (not G) (not H))
    (and A F G (not B) (not C) (not D) (not E) (not H) (not I))
    (and A F H (not B) (not C) (not D) (not E) (not G) (not I))
    (and A F I (not B) (not C) (not D) (not E) (not G) (not H))
    (and A G H (not B) (not C) (not D) (not E) (not F) (not I))
    (and A G I (not B) (not C) (not D) (not E) (not F) (not H))
    (and A H I (not B) (not C) (not D) (not E) (not F) (not G))
    (and B C D (not A) (not E) (not F) (not G) (not H) (not I))
    (and B C E (not A) (not D) (not F) (not G) (not H) (not I))
    (and B C F (not A) (not D) (not E) (not G) (not H) (not I))
    (and B C G (not A) (not D) (not E) (not F) (not H) (not I))
    (and B C H (not A) (not D) (not E) (not F) (not G) (not I))
    (and B C I (not A) (not D) (not E) (not F) (not G) (not H))
    (and B D E (not A) (not C) (not F) (not G) (not H) (not I))
    (and B D F (not A) (not C) (not E) (not G) (not H) (not I))
    (and B D G (not A) (not C) (not E) (not F) (not H) (not I))
    (and B D H (not A) (not C) (not E) (not F) (not G) (not I))
    (and B D I (not A) (not C) (not E) (not F) (not G) (not H))
    (and B E F (not A) (not C) (not D) (not G) (not H) (not I))
    (and B E G (not A) (not C) (not D) (not F) (not H) (not I))
    (and B E H (not A) (not C) (not D) (not F) (not G) (not I))
    (and B E I (not A) (not C) (not D) (not F) (not G) (not H))
    (and B F G (not A) (not C) (not D) (not E) (not H) (not I))
    (and B F H (not A) (not C) (not D) (not E) (not G) (not I))
    (and B F I (not A) (not C) (not D) (not E) (not G) (not H))
    (and B G H (not A) (not C) (not D) (not E) (not F) (not I))
    (and B G I (not A) (not C) (not D) (not E) (not F) (not H))
    (and B H I (not A) (not C) (not D) (not E) (not F) (not G))
    (and C D E (not A) (not B) (not F) (not G) (not H) (not I))
    (and C D F (not A) (not B) (not E) (not G) (not H) (not I))
    (and C D G (not A) (not B) (not E) (not F) (not H) (not I))
    (and C D H (not A) (not B) (not E) (not F) (not G) (not I))
    (and C D I (not A) (not B) (not E) (not F) (not G) (not H))
    (and C E F (not A) (not B) (not D) (not G) (not H) (not I))
    (and C E G (not A) (not B) (not D) (not F) (not H) (not I))
    (and C E H (not A) (not B) (not D) (not F) (not G) (not I))
    (and C E I (not A) (not B) (not D) (not F) (not G) (not H))
    (and C F G (not A) (not B) (not D) (not E) (not H) (not I))
    (and C F H (not A) (not B) (not D) (not E) (not G) (not I))
    (and C F I (not A) (not B) (not D) (not E) (not G) (not H))
    (and C G H (not A) (not B) (not D) (not E) (not F) (not I))
    (and C G I (not A) (not B) (not D) (not E) (not F) (not H))
    (and C H I (not A) (not B) (not D) (not E) (not F) (not G))
    (and D E F (not A) (not B) (not C) (not G) (not H) (not I))
    (and D E G (not A) (not B) (not C) (not F) (not H) (not I))
    (and D E H (not A) (not B) (not C) (not F) (not G) (not I))
    (and D E I (not A) (not B) (not C) (not F) (not G) (not H))
    (and D F G (not A) (not B) (not C) (not E) (not H) (not I))
    (and D F H (not A) (not B) (not C) (not E) (not G) (not I))
    (and D F I (not A) (not B) (not C) (not E) (not G) (not H))
    (and D G H (not A) (not B) (not C) (not E) (not F) (not I))
    (and D G I (not A) (not B) (not C) (not E) (not F) (not H))
    (and D H I (not A) (not B) (not C) (not E) (not F) (not G))
    (and E F G (not A) (not B) (not C) (not D) (not H) (not I))
    (and E F H (not A) (not B) (not C) (not D) (not G) (not I))
    (and E F I (not A) (not B) (not C) (not D) (not G) (not H))
    (and E G H (not A) (not B) (not C) (not D) (not F) (not I))
    (and E G I (not A) (not B) (not C) (not D) (not F) (not H))
    (and E H I (not A) (not B) (not C) (not D) (not F) (not G))
    (and F G H (not A) (not B) (not C) (not D) (not E) (not I))
    (and F G I (not A) (not B) (not C) (not D) (not E) (not H))
    (and F H I (not A) (not B) (not C) (not D) (not E) (not G))
    (and G H I (not A) (not B) (not C) (not D) (not E) (not F))
  )
)

(define-fun conjecture () Bool
  (and no_attacks exactly_three)
)

(assert conjecture)
(check-sat)
(get-model)

