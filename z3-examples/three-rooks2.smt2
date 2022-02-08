; "better" solution, lighter formulas
; - intersect "at least three" and "at most three" to get exactly three while also enforcing
;   the rook moves

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

(define-fun at_least_one_per_row () Bool
  (and
    (or A B C)
    (or C D E)
    (or D E F)
  )
)

(define-fun at_least_one_per_column () Bool
  (and
    (or A D G)
    (or B E H)
    (or C F I)
  )
)

(define-fun at_most_one_per_row () Bool
  (not
    (or
      (and A B) (and A C) (and B C)
      (and D E) (and D F) (and E F)
      (and G H) (and G I) (and H I)
    )
  )
)

(define-fun at_most_one_per_column () Bool
  (not
    (or
      (and A D) (and A G) (and D G)
      (and B E) (and B H) (and E H)
      (and C F) (and C I) (and F I)
    )
  )
)

(define-fun conjecture () Bool
  (and at_least_one_per_row at_least_one_per_column at_most_one_per_row at_most_one_per_column)
)

(assert conjecture)
(check-sat)
(get-model)

