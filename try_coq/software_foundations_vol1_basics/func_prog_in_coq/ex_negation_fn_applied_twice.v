(* for all boolean functions f
    for all inputs to f
      if (f x) returns negb x
      then (f (f x)) returns x *)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros x.
  rewrite -> H.
  rewrite -> H.
  destruct x as [|] eqn:E.
  
  (* case: x true *)
  {
    simpl.
    reflexivity.
  }
  
  (* case: x false *)
  {
    simpl.
    reflexivity.
  }
Qed.