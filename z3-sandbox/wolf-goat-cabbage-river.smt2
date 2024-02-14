; http://cvc4.cs.stanford.edu/wiki/Datatypes

;------------------------------------------------------------------------------
; declare the State: a 4-tuple of Sides which can be {Left, Right}
;------------------------------------------------------------------------------
(declare-datatype Side (
	(Left) (Right)
))

(declare-datatypes
	; list of (datatype arity)
	((State 0))
	; list of declarations
	(
		((New_State
			; (selector term)
	        (WolfLocation (Side))
			; (selector term)
        	(GoatLocation (Side))
        	; (selector term)
   			(CabbageLocation (Side))
   			; (selector term)
        	(FarmerLocation (Side))
        ))
    )
)

; check legality of state
(define-fun is_legal ((s State)) Bool
	(and
		; Farmer has to be with wolf, or wolf must be separate from goat
		(or (= (FarmerLocation s) (WolfLocation s)) (distinct (WolfLocation s) (GoatLocation s)))
		; Farmer has to be with goat, or goat must be separate from cabbage
		(or (= (FarmerLocation s) (GoatLocation s)) (distinct (GoatLocation s) (CabbageLocation s)))
	)
)

;------------------------------------------------------------------------------
; define the functions that "manipulate" (create new versions of) the state
;------------------------------------------------------------------------------
; flips the side
(define-fun flip ((x Side)) Side
	(ite (= x Left) Right Left)
)

; does not check legality
(define-fun do_cross_wolf ((s State)) State
	(New_State (flip (WolfLocation s)) (GoatLocation s) (CabbageLocation s) (flip (FarmerLocation s)))
)
(define-fun do_cross_goat ((s State)) State
	(New_State (WolfLocation s) (flip (GoatLocation s)) (CabbageLocation s) (flip (FarmerLocation s)))
)
(define-fun do_cross_cabbage ((s State)) State
	(New_State (WolfLocation s) (GoatLocation s) (flip (CabbageLocation s)) (flip (FarmerLocation s)))
)
(define-fun do_cross_farmer ((s State)) State
	(New_State (WolfLocation s) (GoatLocation s) (CabbageLocation s) (flip (FarmerLocation s)))
)
(define-fun do_cross_nothing ((s State)) State
	(New_State (WolfLocation s) (GoatLocation s) (CabbageLocation s) (FarmerLocation s))
)

;------------------------------------------------------------------------------
; define the moves
;------------------------------------------------------------------------------
(declare-datatype Move (
	(CrossWolf) (CrossGoat) (CrossCabbage) (CrossFarmer) (CrossNothing)
))

(declare-const move0 Move)
(declare-const move1 Move)
(declare-const move2 Move)
(declare-const move3 Move)
(declare-const move4 Move)
(declare-const move5 Move)
(declare-const move6 Move)

(define-fun apply_move ((s State) (m Move)) State
	(match m
		(
			((CrossWolf) (do_cross_wolf s))
			((CrossGoat) (do_cross_goat s))
			((CrossCabbage) (do_cross_cabbage s))
			((CrossFarmer) (do_cross_farmer s))
			((CrossNothing) (do_cross_nothing s))
		)
	)
)

;------------------------------------------------------------------------------
; set up the constraints, solve!
;------------------------------------------------------------------------------

; start state is everyone to the left
(define-const state0 State
	(New_State Left Left Left Left)
)

; goal state is everyone to the right
(define-const state_solved State
	(New_State Right Right Right Right)
)

; unknown intermediate states
(define-const state1 State (apply_move state0 move0))
(define-const state2 State (apply_move state1 move1))
(define-const state3 State (apply_move state2 move2))
(define-const state4 State (apply_move state3 move3))
(define-const state5 State (apply_move state4 move4))
(define-const state6 State (apply_move state5 move5))
(define-const state7 State (apply_move state6 move6))

(assert (is_legal state1))
(assert (is_legal state2))
(assert (is_legal state3))
(assert (is_legal state4))
(assert (is_legal state5))
(assert (is_legal state6))
(assert (= state7 state_solved))

(check-sat)
(get-value (move0 move1 move2 move3 move4 move5 move6))
