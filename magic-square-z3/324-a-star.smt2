; 324. A Star from The Moscow Puzzles

;        A
;       / \
;  B - C - D - E
;   \ /     \ /
;    F       G
;   / \     / \
;  H - I - J - K
;       \ /
;        L

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
(declare-const j Int)
(declare-const k Int)
(declare-const l Int)

(assert (= (+ a (+ d (+ g k)) 26)))
(assert (= (+ e (+ g (+ j l)) 26)))
(assert (= (+ k (+ j (+ i h)) 26)))
(assert (= (+ l (+ i (+ f b)) 26)))
(assert (= (+ h (+ f (+ c a)) 26)))
(assert (= (+ b (+ c (+ d e)) 26)))

(assert (and (>= a 1) (<= a 12)))
(assert (and (>= b 1) (<= b 12)))
(assert (and (>= c 1) (<= c 12)))
(assert (and (>= d 1) (<= d 12)))
(assert (and (>= e 1) (<= e 12)))
(assert (and (>= f 1) (<= f 12)))
(assert (and (>= g 1) (<= g 12)))
(assert (and (>= h 1) (<= h 12)))
(assert (and (>= i 1) (<= i 12)))
(assert (and (>= j 1) (<= j 12)))
(assert (and (>= k 1) (<= k 12)))
(assert (and (>= l 1) (<= l 12)))

(assert (distinct a b c d e f g h i j k l))

(check-sat)
(get-model)

;        1
;       / \
;  2 - 3 - 4 - 5 
;   \ /     \ /
;    6       7
;   / \     / \
;  8 - 9 - 10- 11
;       \ /
;        12
