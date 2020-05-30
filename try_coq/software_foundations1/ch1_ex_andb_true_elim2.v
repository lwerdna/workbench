(* had to cheat to see that this proof requires false to be rewritten!
  see https://www.cs.cmu.edu/~emc/15414-s14/lecture/lecture_2_17_2014.v *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

Proof.
  intros b c.
  intros H. (* suppose andb b c = true *)
  destruct c as [|] eqn:E.
  - (* case: c is true, then yay, c = true *)
    reflexivity.
  - (* case: c is false
      H = andb b false = true *)
    rewrite <- H.
    destruct b as [|] eqn:F.
    + (* case: b is true *)
    reflexivity.
    + (* case: b is false *)
    reflexivity.
Qed.

