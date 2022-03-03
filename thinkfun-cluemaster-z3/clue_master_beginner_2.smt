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
(assert (IsBowl p1))
(assert (IsBowl p4))
(assert (IsBall p7))

; clue #2
(assert (IsBlue p1))
(assert (IsBlue p2))
(assert (IsBlue p3))

; clue #3
(assert (IsGreen p4))
(assert (IsGreen p5))
(assert (IsGreen p6))

; clue #4
(assert (IsBone p3))
(assert (IsBall p6))
(assert (IsBowl p9))

(check-sat)
(get-model)
