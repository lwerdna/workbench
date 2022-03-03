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
	(and (IsBlue p1) (IsBall p1) (IsGreen p5) (IsBowl p5))
	(and (IsBlue p2) (IsBall p2) (IsGreen p6) (IsBowl p6))
	(and (IsBlue p4) (IsBall p4) (IsGreen p8) (IsBowl p8))
	(and (IsBlue p5) (IsBall p5) (IsGreen p9) (IsBowl p9))			
))

; clue #2
(assert (or
	(and (IsGreen p1) (IsBone p1))
	(and (IsGreen p2) (IsBone p2))
))

; clue #3
(assert (or
	(and (IsGreen p4) (IsBall p4))
	(and (IsGreen p5) (IsBall p5))
	(and (IsGreen p6) (IsBall p6))
))

; clue #4
(assert (or
	(and (IsBowl p2) (IsBowl p4))
	(and (IsBowl p3) (IsBowl p5))
	(and (IsBowl p5) (IsBowl p7))
	(and (IsBowl p6) (IsBowl p8))
))

; clue #5
(assert (or
	(and (IsRed p1) (IsBall p1))
	(and (IsRed p2) (IsBall p2))
	(and (IsRed p4) (IsBall p4))
	(and (IsRed p5) (IsBall p5))
))

; clue #6
(assert (or
	(and (IsGreen p1) (IsBone p1) (IsBowl p2) (IsRed p4))
	(and (IsGreen p2) (IsBone p2) (IsBowl p3) (IsRed p5))
	(and (IsGreen p4) (IsBone p4) (IsBowl p5) (IsRed p7))
	(and (IsGreen p5) (IsBone p5) (IsBowl p6) (IsRed p8))
))

; clue #7
(assert (not (or
	(IsBall p2)
	(IsBall p5)
	(IsBall p8)
)))

; clue #8
(assert (not (or
	(IsRed p4)
	(IsRed p7)
)))

; clue #9
(assert (not (or
	(IsGreen p1)
	(IsGreen p4)
	(IsGreen p7)
)))

(check-sat)
(get-model)
