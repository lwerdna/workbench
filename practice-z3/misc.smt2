; all possible commands are in Figure 3.6: SMT-LIB Commands in the II.Syntax > Scripts section
; of SMT-LIB Standard Version 2.6 Release: 2017-07-18

; find a solution for:
; (x + x + y) * (/x + /y + /y) * (/x + y + y)
(declare-const x Bool)
(declare-const y Bool)
(assert (and (or x x y) (or (not x) (not y) (not y)) (or (not x) y y)))
(check-sat)
;(get-model)
(get-value (x y))

; a const is a zero-argument ("nullary") function without side effects ("pure")
(reset)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (and (or x x y) (or (not x) (not y) (not y)) (or (not x) y y)))
(check-sat)
;(get-model)
(get-value (x y))

; the constraint expression can be abstracted into a function, and the function asserted
(reset)
(declare-fun x () Bool)
(declare-fun y () Bool)
(define-fun problem ((a Bool) (b Bool)) Bool
  (and (or a a b) (or (not a) (not b) (not b)) (or (not a) b b))
)
(assert (problem x y))
(check-sat)
;(get-model)
(get-value (x y))

(echo "-- prove p or not p by solving for a counterexample")
(reset)
(declare-const p Bool)
(define-fun conjecture () Bool (or p (not p)))
(assert (not conjecture))
(check-sat)

(echo "-- prove transitivity of implication by solving for a counterexample")
(reset)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(define-fun conjecture () Bool
	(=>
		(and			; p->q and q->r
			(=> p q)
			(=> q r)
		)
		(=> p r)		; p->r
	)
)
(assert (not conjecture))
(check-sat)

(echo "-- synthesize NOT")
; you can solve for functions
(reset)
(declare-fun blackbox (Bool) Bool)
(assert (blackbox false))
(assert (not (blackbox true)))
(check-sat)
(get-model)
;(get-value (blackbox))

(echo "-- synthesize XOR")
(reset)
(declare-fun blackbox (Bool Bool) Bool)
(assert (not (blackbox false false)))
(assert      (blackbox false true))
(assert      (blackbox true false))
(assert (not (blackbox true true)))
(check-sat)
(get-model)
;(get-value (blackbox))

; solving for a function that behaves like another function
(reset)

; /a/b/c + /ab + ab/c + ac
(define-fun complicated ((a Bool) (b Bool) (c Bool)) Bool
  (or (and (not a) (not b) (not c))
      (and (not a) b)
      (and a b (not c))
      (and a c)
  )
)
(assert (= (complicated false false false) true))
(assert (= (complicated false false true) false))
(assert (= (complicated false true false) true))
(assert (= (complicated false true true) true))
(assert (= (complicated true false false) false))
(assert (= (complicated true false true) true))
(assert (= (complicated true true false) true))
(assert (= (complicated true true true) true))
(echo "-- does complicated() behave as expected?")
(check-sat)

; attempt #1: set the function bodies equal to each other
; this produced "unknown"
(echo "-- simplify test #1")
(declare-fun simplified (Bool Bool Bool) Bool)
(assert (= complicated simplified))
(check-sat)

; attempt #2: set the function bodies applied to three variables equal to each other
; this is a mistake: Z3 can just assign also x, y, z
; it produces x=false, y=false, z=false, simplified(a,b,c) = /a/b/c
; and indeed simplified(x,y,z) = complicated(x,y,z) = true
(reset-assertions)
(echo "-- simplify test #2")
(declare-fun x () Bool)
(declare-fun y () Bool)
(declare-fun z () Bool)
(assert (= (complicated x y z) (simplified x y z)))
(check-sat)
(get-model)

; attempt #3: set the functions equal applied to all possible inputs
; this works but produces a terribly complicated function
(echo "-- simplify test #3")
(reset-assertions)
(assert (= (complicated false false false) (simplified false false false)))
(assert (= (complicated false false true) (simplified false false true)))
(assert (= (complicated false true false) (simplified false true false)))
(assert (= (complicated false true true) (simplified false true true)))
(assert (= (complicated true false false) (simplified true false false)))
(assert (= (complicated true false true) (simplified true false true)))
(assert (= (complicated true true false) (simplified true true false)))
(assert (= (complicated true true true) (simplified true true true)))
(check-sat)
(get-model)

; attempt #4: using quantifier
(echo "-- simplify test #4")
(reset-assertions)
(echo "4")
(assert (forall ((a Bool) (b Bool) (c Bool)) (= (simplified a b c) (complicated a b c))))
(check-sat)
(get-model)

