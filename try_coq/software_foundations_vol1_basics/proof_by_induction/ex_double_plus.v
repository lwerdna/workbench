Load ex_basic_induction.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,
  double n = n + n .
Proof.
  intros n.
  induction n as [| k IH].
  (* base case: n=0 *)
  reflexivity.
  (* IH: k = k + k
    then (S k) = (S k) + (S k)
  *)
  simpl.
  rewrite plus_comm.
  simpl.
  rewrite IH.
  reflexivity.
Qed.