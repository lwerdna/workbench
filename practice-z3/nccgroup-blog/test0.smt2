; https://research.nccgroup.com/2021/01/29/software-verification-and-analysis-using-z3/

(declare-const largest-pn  (_ BitVec 64))
(declare-const truncated-pn  (_ BitVec 64))
(declare-const pn-nbits  (_ BitVec 64))
(declare-const expected-pn  (_ BitVec 64))
(declare-const pn-win  (_ BitVec 64))
(declare-const pn-hwin  (_ BitVec 64))
(declare-const pn-mask  (_ BitVec 64))
(declare-const candidate-pn  (_ BitVec 64))
(declare-const result  (_ BitVec 64))

; truncated-pn <= 2^32-1 when bits interpreted as unsigned integer
(assert (bvule truncated-pn (_ bv4294967295 64))) 

; 0 <= largest-pn <= 2^62-1 when bits interpreted as unsigned integer
(assert (bvule largest-pn (_ bv4611686018427387903 64))); largest-pn <= 2^62-1
(assert (bvuge largest-pn (_ bv0 64))) ; largest-pn >= 0

; pn-bits \in {8, 16, 24, 32}
(assert (or (= pn-nbits (_ bv8 64))
        (= pn-nbits (_ bv16 64))
        (= pn-nbits (_ bv24 64))
        (= pn-nbits (_ bv32 64))))

;; ensure that truncated-pn is < 2^pn-bits and >= 2^(pn-bits-8)
;; This may not not be the case in an adverse scenario
(assert
 (and
  (bvult truncated-pn (bvshl (_ bv1 64) pn-nbits))
  (bvuge truncated-pn (bvshl (_ bv1 64) (bvsub pn-nbits (_ bv8 64))))))

;C:
; expected_pn = largest_pn + 1
(assert (= expected-pn (bvadd largest-pn (_ bv1 64))))

;C:
; pn_win       = 1 << pn_nbits
(assert(= pn-win
       (bvshl (_ bv1 64) pn-nbits)))

;C:
; pn_hwin = pn_win / 2
(assert (=  pn-hwin 
         (bvlshr pn-win (_ bv1 64) )))

;C:
; pn_mask = pn_win - 1
(assert (= pn-mask
       (bvsub pn-win (_ bv1 64) )))

;C:
; candidate_pn = (expected_pn ~pn_mask) | truncated_pn
(assert (= candidate-pn
       (bvor
        (bvand expected-pn (bvnot pn-mask))
        truncated-pn)))

;C:
;  if (candidate_pn <= expected_pn - pn_hwin)
;		return candidate_pn + pn_win;
;  if candidate_pn > expected_pn + pn_hwin and
;     candidate_pn > pn_win:
;        return candidate_pn - pn_win
;
;  return candidate_pn

; which can be rewritten as:

; if (candidate_pn <= expected_pn - pn_hwin)
;     result = candidate_pn + pn_win
; else if (candidate_pn > expected_pn + pn_hwin && candidate_pn > pn_win)
;     result = candidate_pn - pn_win
; else
;     result = candidate_pn
(assert
  (= result 
	(ite (bvule candidate-pn (bvsub expected-pn pn-hwin))
		(bvadd candidate-pn pn-win)
		(ite (and (bvugt candidate-pn (bvadd expected-pn pn-win)) (bvugt candidate-pn pn-win))
		  (bvsub candidate-pn pn-win)
		  candidate-pn
		)
	)
  )
)

(push 1)
; For example, if the highest successfully authenticated packet had a packet number of 0xa82f30ea,
; then a packet containing a 16-bit value of 0x9b32 will be decoded as 0xa82f9b32.
(assert (and
     ;(= largest-pn (_ bv2821665002 64))
     (= largest-pn #x00000000A82F30EA)
     (= pn-nbits (_ bv16 64))
     (= truncated-pn #x0000000000009B32)
     (= result #x00000000A82F9B32)
))

(check-sat)
(get-model)
(pop 1)

(push 1)
(assert (bvugt result #x3fffffffffffffff))
(check-sat)
;(get-model)
(get-value (largest-pn truncated-pn pn-nbits))
(pop 1)

(push 1)
(assert (bvugt result #x3fffffffffffffff))
(assert (= pn-nbits (_ bv16 64)))
(check-sat)
;(get-model)
(get-value (largest-pn truncated-pn pn-nbits))
(pop 1)

(push 1)
(assert (bvugt result #x3fffffffffffffff))
(assert (not (= largest-pn #x3fffffffffffffff)))
(check-sat)
;(get-model)
(get-value (largest-pn truncated-pn pn-nbits))
(pop 1)

(push 1)
(assert (bvugt result #x3fffffffffffffff))
(assert (not (= largest-pn #x3fffffffffffffff)))
(assert (= pn-nbits (_ bv32 64)))
(check-sat)
;(get-model)
(get-value (largest-pn truncated-pn pn-nbits))
(pop 1)
