(* for all boolean functions f
    for all inputs to f
      if (f x) returns x
      then (f (f x)) returns x *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros x.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.