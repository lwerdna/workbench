(* standard enumerated type, listing the set/type elements *)
Inductive bit : Type :=
  | B0
  | B1.

(* nybble type with constructor bits which takes a tuple of bit *)
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

(* ==> bits B1 B0 B1 B0 : nybble *)

(* use constructor matching to determine if nybble is all zeros *)
Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)
