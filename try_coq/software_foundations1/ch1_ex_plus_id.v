Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
  
Proof.
  intros n m o.
  intros H1. (* hypothesis that n = m *)
  intros H2. (* hypothesis that m = o *)
  rewrite -> H1. (* replace n with m *)
  rewrite <- H2. (* replace o with m *)
  reflexivity.
Qed.