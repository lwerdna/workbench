(* (and true x) = x *)
Lemma and_true_x_is_x : forall x : bool,
  andb true x = x.
Proof.
  intros x.
  reflexivity.
Qed.

(* (and false x) = false *)
Lemma and_false_x_is_false : forall x : bool,
  andb false x = false.
Proof.
  intros x.
  reflexivity.
Qed.

(* (or true x) = true *)
Lemma or_true_x_is_true : forall x : bool,
  orb true x = true.
Proof.
  intros x.
  reflexivity.
Qed.

(* (or false x) = false *)
Lemma or_false_x_is_x : forall x : bool,
  orb false x = x.
Proof.
  intros x.
  reflexivity.
Qed.

(* if and(b,c) = or(b,c) -> b = c *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.

Proof.
  intros b c.
  intros H.
  destruct b as [|] eqn:E.
  (* b=true *)
  {
    rewrite and_true_x_is_x in H.
    rewrite or_true_x_is_true in H.
    rewrite H.
    reflexivity.
  }
  {
    rewrite or_false_x_is_x in H.
    rewrite and_false_x_is_false in H.
    rewrite H.
    reflexivity.
  }
Qed.
