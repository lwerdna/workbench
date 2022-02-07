; 325. A Crystal from The Moscow Puzzles
;
; additionally, all variables <= 13

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
(declare-const m Int)

(assert (= (+ a (+ b c)) 20))
(assert (= (+ c (+ h m)) 20))
(assert (= (+ m (+ l k)) 20))
(assert (= (+ k (+ f a)) 20))

(assert (= (+ b (+ e h)) 20))
(assert (= (+ h (+ j l)) 20))
(assert (= (+ l (+ i f)) 20))
(assert (= (+ f (+ d b)) 20))

(assert (= (+ d (+ g j)) 20))
(assert (= (+ i (+ g e)) 20))

(assert (and (>= a 1) (<= a 13)))
(assert (and (>= b 1) (<= b 13)))
(assert (and (>= c 1) (<= c 13)))
(assert (and (>= d 1) (<= d 13)))
(assert (and (>= e 1) (<= e 13)))
(assert (and (>= f 1) (<= f 13)))
(assert (and (>= g 1) (<= g 13)))
(assert (and (>= h 1) (<= h 13)))
(assert (and (>= i 1) (<= i 13)))
(assert (and (>= j 1) (<= j 13)))
(assert (and (>= k 1) (<= k 13)))
(assert (and (>= l 1) (<= l 13)))
(assert (and (>= m 1) (<= m 13)))

; (assert (distinct a b c d e f g h i j k l m))

(assert
	(or
		(and (= a b) (distinct c d e f g h i j k l m))
		(and (= a c) (distinct b d e f g h i j k l m))
		(and (= a d) (distinct b c e f g h i j k l m))
		(and (= a e) (distinct b c d f g h i j k l m))
		(and (= a f) (distinct b c d e g h i j k l m))
		(and (= a g) (distinct b c d e f h i j k l m))
		(and (= a h) (distinct b c d e f g i j k l m))
		(and (= a i) (distinct b c d e f g h j k l m))
		(and (= a j) (distinct b c d e f g h i k l m))
		(and (= a k) (distinct b c d e f g h i j l m))
		(and (= a l) (distinct b c d e f g h i j k m))
		(and (= a m) (distinct b c d e f g h i j k l))
		(and (= b c) (distinct a d e f g h i j k l m))
		(and (= b d) (distinct a c e f g h i j k l m))
		(and (= b e) (distinct a c d f g h i j k l m))
		(and (= b f) (distinct a c d e g h i j k l m))
		(and (= b g) (distinct a c d e f h i j k l m))
		(and (= b h) (distinct a c d e f g i j k l m))
		(and (= b i) (distinct a c d e f g h j k l m))
		(and (= b j) (distinct a c d e f g h i k l m))
		(and (= b k) (distinct a c d e f g h i j l m))
		(and (= b l) (distinct a c d e f g h i j k m))
		(and (= b m) (distinct a c d e f g h i j k l))
		(and (= c d) (distinct a b e f g h i j k l m))
		(and (= c e) (distinct a b d f g h i j k l m))
		(and (= c f) (distinct a b d e g h i j k l m))
		(and (= c g) (distinct a b d e f h i j k l m))
		(and (= c h) (distinct a b d e f g i j k l m))
		(and (= c i) (distinct a b d e f g h j k l m))
		(and (= c j) (distinct a b d e f g h i k l m))
		(and (= c k) (distinct a b d e f g h i j l m))
		(and (= c l) (distinct a b d e f g h i j k m))
		(and (= c m) (distinct a b d e f g h i j k l))
		(and (= d e) (distinct a b c f g h i j k l m))
		(and (= d f) (distinct a b c e g h i j k l m))
		(and (= d g) (distinct a b c e f h i j k l m))
		(and (= d h) (distinct a b c e f g i j k l m))
		(and (= d i) (distinct a b c e f g h j k l m))
		(and (= d j) (distinct a b c e f g h i k l m))
		(and (= d k) (distinct a b c e f g h i j l m))
		(and (= d l) (distinct a b c e f g h i j k m))
		(and (= d m) (distinct a b c e f g h i j k l))
		(and (= e f) (distinct a b c d g h i j k l m))
		(and (= e g) (distinct a b c d f h i j k l m))
		(and (= e h) (distinct a b c d f g i j k l m))
		(and (= e i) (distinct a b c d f g h j k l m))
		(and (= e j) (distinct a b c d f g h i k l m))
		(and (= e k) (distinct a b c d f g h i j l m))
		(and (= e l) (distinct a b c d f g h i j k m))
		(and (= e m) (distinct a b c d f g h i j k l))
		(and (= f g) (distinct a b c d e h i j k l m))
		(and (= f h) (distinct a b c d e g i j k l m))
		(and (= f i) (distinct a b c d e g h j k l m))
		(and (= f j) (distinct a b c d e g h i k l m))
		(and (= f k) (distinct a b c d e g h i j l m))
		(and (= f l) (distinct a b c d e g h i j k m))
		(and (= f m) (distinct a b c d e g h i j k l))
		(and (= g h) (distinct a b c d e f i j k l m))
		(and (= g i) (distinct a b c d e f h j k l m))
		(and (= g j) (distinct a b c d e f h i k l m))
		(and (= g k) (distinct a b c d e f h i j l m))
		(and (= g l) (distinct a b c d e f h i j k m))
		(and (= g m) (distinct a b c d e f h i j k l))
		(and (= h i) (distinct a b c d e f g j k l m))
		(and (= h j) (distinct a b c d e f g i k l m))
		(and (= h k) (distinct a b c d e f g i j l m))
		(and (= h l) (distinct a b c d e f g i j k m))
		(and (= h m) (distinct a b c d e f g i j k l))
		(and (= i j) (distinct a b c d e f g h k l m))
		(and (= i k) (distinct a b c d e f g h j l m))
		(and (= i l) (distinct a b c d e f g h j k m))
		(and (= i m) (distinct a b c d e f g h j k l))
		(and (= j k) (distinct a b c d e f g h i l m))
		(and (= j l) (distinct a b c d e f g h i k m))
		(and (= j m) (distinct a b c d e f g h i k l))
		(and (= k l) (distinct a b c d e f g h i j m))
		(and (= k m) (distinct a b c d e f g h i j l))
		(and (= l m) (distinct a b c d e f g h i j k))
	)
)

(check-sat)
(get-model)
