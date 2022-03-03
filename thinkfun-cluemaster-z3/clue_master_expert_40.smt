(declare-datatypes () ((Item RedBall RedBowl RedBone GreenBall GreenBowl GreenBone BlueBall BlueBowl BlueBone)))
(declare-const p1 Item)
(declare-const p2 Item)
(declare-const p3 Item)
(declare-const p4 Item)
(declare-const p5 Item)
(declare-const p6 Item)
(declare-const p7 Item)
(declare-const p8 Item)
(declare-const p9 Item)

; color checks
(define-fun IsRed ((x Item)) Bool (or (= x RedBall) (= x RedBowl) (= x RedBone)))
(define-fun IsGreen ((x Item)) Bool (or (= x GreenBall) (= x GreenBowl) (= x GreenBone)))
(define-fun IsBlue ((x Item)) Bool (or (= x BlueBall) (= x BlueBowl) (= x BlueBone)))

; item checks
(define-fun IsBall ((x Item)) Bool (or (= x RedBall) (= x GreenBall) (= x BlueBall)))
(define-fun IsBowl ((x Item)) Bool (or (= x RedBowl) (= x GreenBowl) (= x BlueBowl)))
(define-fun IsBone ((x Item)) Bool (or (= x RedBone) (= x GreenBone) (= x BlueBone)))

(declare-const Red (List Item))

(assert (distinct p1 p2 p3 p4 p5 p6 p7 p8 p9))

; clue #1
(assert (or 
	(IsBall p1)
	(IsBall p2)
))

; clue #2
(assert (or
	(and (IsGreen p1) (IsBowl p6))
	(and (IsGreen p4) (IsBone p9))
))

; clue #3
(assert (or
	(and (IsGreen p1) (IsGreen p3))
	(and (IsGreen p3) (IsGreen p6))
	(and (IsGreen p7) (IsGreen p9))
))

; clue #4
(assert (or
	(and (IsRed p3) (IsBone p3))
	(and (IsRed p6) (IsBone p6))
	(and (IsRed p9) (IsBone p9))
))

; clue #5
(assert (not (or
	(and (IsBall p1) (IsBone p4))
	(and (IsBall p2) (IsBone p5))
	(and (IsBall p3) (IsBone p6))
	(and (IsBall p4) (IsBone p7))
	(and (IsBall p5) (IsBone p8))
	(and (IsBall p6) (IsBone p9))
)))

; clue #6
(assert (not (or
	(IsBowl p4)
	(IsBowl p5)
	(IsBowl p7)
	(IsBowl p8)
)))

; clue #7
(assert (not (or
	(and (IsBone p1) (IsBall p2) (IsBone p4))
	(and (IsBone p2) (IsBall p3) (IsBone p5))
	(and (IsBone p4) (IsBall p5) (IsBone p7))
	(and (IsBone p5) (IsBall p6) (IsBone p8))
)))

; clue #8
(assert (not (or
	(and (IsBowl p1) (IsRed p2))
	(and (IsBowl p2) (IsRed p3))
	(and (IsBowl p4) (IsRed p5))
	(and (IsBowl p5) (IsRed p6))
	(and (IsBowl p7) (IsRed p8))
	(and (IsBowl p8) (IsRed p9))
)))

; clue #9
(assert (not (or
	(and (IsBlue p1) (IsRed p3))
	(and (IsBlue p4) (IsRed p6))
	(and (IsBlue p7) (IsRed p9))
)))

(check-sat)
(get-model)
