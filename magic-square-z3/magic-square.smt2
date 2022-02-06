; standard 3x3 magic square puzzle
;
; a b c
; d e f
; g h i
;
; where every row, column, and diagonal must sum to 15

(set-logic QF_LIA)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)
(declare-const f Int)
(declare-const g Int)
(declare-const h Int)
(declare-const i Int)

(assert (and (= (+ a (+ b c)) 15)
             (= (+ d (+ e f)) 15)
             (= (+ g (+ h i)) 15)

             (= (+ a (+ d g)) 15)
             (= (+ b (+ e h)) 15)
             (= (+ c (+ f i)) 15)

             (= (+ a (+ e i)) 15)
             (= (+ g (+ e c)) 15)))

(assert (and (>= a 1) (<= a 9)))
(assert (and (>= b 1) (<= b 9)))
(assert (and (>= c 1) (<= c 9)))
(assert (and (>= d 1) (<= d 9)))
(assert (and (>= e 1) (<= e 9)))
(assert (and (>= f 1) (<= f 9)))
(assert (and (>= g 1) (<= g 9)))
(assert (and (>= h 1) (<= h 9)))
(assert (and (>= i 1) (<= i 9)))

(assert (distinct a b c d e f g h i))

(check-sat)
(get-model)
