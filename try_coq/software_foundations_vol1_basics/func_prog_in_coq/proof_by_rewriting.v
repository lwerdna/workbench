Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis (n = m) into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis:
    before: n + n = m + m
     after: m + m = m + m

    note this arrow is NOT implication, it's the direction
    of the rewrite (do I switch n's with m's or visa versa)
  *)
  rewrite <- H.
  (* check equality *)
  reflexivity.
Qed.  

(*
Theorem theyre_the_same : forall n m o : nat,
  n = m and m = o -> n = o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.
*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1. (* rewrite, left-to-right, using H1 *)
  rewrite <- H2.
  reflexivity.
Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

(* adding 1 is the same as the successor *) 
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.
