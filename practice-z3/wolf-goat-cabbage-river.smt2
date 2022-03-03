; http://cvc4.cs.stanford.edu/wiki/Datatypes
;
; (declare-datatypes ((D1 n1)...(Dk nk)) 
;   (((C1 (S1 T1)....(Si Ti))...(Cj .... ))
;    ...
;    ((....) ... (....)))

; D1 n1 are datatype types
;
; D1,n1 = Objects,0
; C1,C2,C3,C4 = Man,Wolf,Goat,Cabbage
(declare-datatype Object (
	(Man) (Wolf) (Goat) (Cabbage)
))

; make some uninitialized ("unintepreted") Objects
; a const is a nullary function, so declare-const is shorthand for: (declare-fun a () Object)
(declare-const a Object)
(declare-const b Object)

; make some initialized ("interpreted") Objects
(define-fun manobj () Object Man)
(define-fun wolfobj () Object Wolf)
(define-fun goatobj () Object Goat)

(assert (and (not (= a Man)) (not (= a Wolf)) (not (= a Goat))))
(check-sat)
;(get-model)
(get-value (a b))

; make some known Objects
;(declare-const c Man)

; a list of objects
; D1,n1 = list,0
; C1 = cons, S1,T1 = head,Object
;            S2,T2 = tail,list
; C2 = nil
(declare-datatypes ((list 0)) 
    (((cons (head Object) (tail list)) (nil))))

;
;(declare-datatype ((state 0))
;	(((side_a (list Object) (
