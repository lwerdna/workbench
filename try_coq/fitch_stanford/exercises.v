Theorem conjunction_elimination_left : forall a b : bool,
  (andb a b)=true -> a=true.
Proof.
  intros a b.
  intros H1.
  destruct a as [|] eqn:E.
    (* case: a is true *)
    reflexivity.
    (* case: a is false *)
    rewrite <- H1.
    simpl.
    reflexivity.
Qed.

(* http://intrologic.stanford.edu/exercises/exercise_04_02.html *)
Theorem fitch_04_02 : forall p q : bool,
  (andb p q)=true -> (orb p q)=true.
Proof.
  intros p q.
  intros H.
  apply conjunction_elimination_left in H.
  rewrite H.
  simpl.
  reflexivity.
Qed.
