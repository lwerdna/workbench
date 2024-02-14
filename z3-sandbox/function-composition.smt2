; can z3 map thru function compositions?
; f(x) maps English word to Int
; g(x) maps Int to its square Int
; h(x) maps Int to Spanish word

; can z3 solve for x in h(g(f(x))) = Nueve ?

; http://cvc4.cs.stanford.edu/wiki/Datatypes
(declare-datatype English (
	(One) (Two) (Three) (Four) (Five)
	(Six) (Seven) (Eight) (Nine) (Ten)
))

(declare-datatype Spanish (
	(Uno) (Dos) (Tres) (Cuatro) (Cinco)
	(Seis) (Siete) (Ocho) (Nueve) (Diez) (Nada)
))

(define-fun f ((x English)) Int
	(ite (= x One) 1
	(ite (= x Two) 2
	(ite (= x Three) 3
	(ite (= x Four) 4
	(ite (= x Five) 5
	(ite (= x Six) 6
	(ite (= x Seven) 7
	(ite (= x Eight) 8
	(ite (= x Nine) 9
	(ite (= x Ten) 10 -1
	))))))))))
)

(define-fun g ((x Int)) Int
	(ite (= x 1) 1
	(ite (= x 2) 4
	(ite (= x 3) 9
	(ite (= x 4) 16
	(ite (= x 5) 25
	(ite (= x 6) 36
	(ite (= x 7) 49
	(ite (= x 8) 64
	(ite (= x 9) 81
	(ite (= x 10) 100 -1
	))))))))))
)

(define-fun h ((x Int)) Spanish
	(ite (= x 1) Uno
	(ite (= x 2) Dos
	(ite (= x 3) Tres
	(ite (= x 4) Cuatro
	(ite (= x 5) Cinco
	(ite (= x 6) Seis
	(ite (= x 7) Siete
	(ite (= x 8) Ocho
	(ite (= x 9) Nueve
	(ite (= x 10) Diez Nada
	))))))))))
)

(declare-const x English)

(assert (= (h (g (f x))) Nueve))
(check-sat)
(get-value (x))
