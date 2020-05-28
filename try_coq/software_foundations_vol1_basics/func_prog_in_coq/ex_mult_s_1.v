Lemma plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
  
Proof.
  intros n m.
  intros H. (* suppose m = S n *)
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.