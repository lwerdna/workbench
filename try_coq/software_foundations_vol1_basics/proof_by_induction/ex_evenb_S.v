Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Theorem double_neg : forall x : bool,
  (negb (negb x)) = x.
Proof.
  intros x.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Print nat.

(* evenness of n is opposite evenness of (S n) *)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
  
Proof.
  intros n.
  (* case analysis *)
  induction n as [|k IH].
  (* n:nat constructed with first constructor: | O : nat *)
  simpl.
  reflexivity.
  (* n:nat constructed with second constructor: | S : nat -> nat *)
  rewrite IH.
  simpl.
  rewrite double_neg.
  reflexivity.
Qed.