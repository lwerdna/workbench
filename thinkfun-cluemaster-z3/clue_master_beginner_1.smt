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
(assert (IsGreen p1))

(assert (IsBone p2))
(assert (IsBlue p2))

(assert (IsBall p3))
(assert (IsRed p3))

(assert (IsBone p4))
(assert (IsRed p4))

(assert (IsBone p5))
(assert (IsGreen p5))

(assert (IsBowl p6))
(assert (IsBlue p6))

(assert (IsBall p7))

(assert (IsRed p8))

(assert (IsBlue p9))

(check-sat)
(get-model)
