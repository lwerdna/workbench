Theorem modus_ponens: forall a b: Prop,
  a /\ (a -> b) -> b.
Proof.
  intros a b H.
  destruct H.
  apply H0 in H as b_holds.
  assumption.
Qed.

Theorem modus_ponens2 : forall a b: bool,
  a=true /\ (a=true -> b=true) -> b=true.
Proof.
  intros a b.
  intros H.
  destruct H.
  specialize (H0 H).
  rewrite H0.
  reflexivity.
Qed.

(* Tuplanolla on freenode #coq calls this reflection *)
