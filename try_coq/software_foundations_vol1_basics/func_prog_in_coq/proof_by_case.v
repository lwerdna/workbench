Fixpoint does_equal (n m : nat) : bool :=
  match n with
  | O =>
    match m with
    | O => true
    | S m' => false
    end
  | S n' =>
    match m with
    | O => false
    | S m' => does_equal n' m'
    end
  end.

Notation "x =? y" := (does_equal x y) (at level 70) : nat_scope.

Theorem no_nums_successor_is_0 : forall n : nat,
  (S n =? O) = false.

Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.

Proof.
  intros n.
  simpl. (* does nothing! why? 
    it can't use S constructor because n is unknown variable *)
Abort.


Theorem plus_1_neq_0_secondtry : forall n : nat,
  (n + 1) =? 0 = false.

Proof.
  intros n.
  (* "[| n']" is an intro argument
  (nothing) in first, since O constructor is nullary
          n in second, since S is unary

  E is the name of resulting equations
  *)

  (* destruct <a> as [| foo] eqn:E
      splits a into O and ???
      sends nothing to constructor O for first case (E: n = 0)
      sends b to constructor sa for second case (E: n = S foo)

      E will hold
    *)
  destruct n as [| foo] eqn:E.
  - (* bullet, do subproof for first subgoal *)
  simpl.
  reflexivity.
  - (* bullet, do subproof for second subgoal *)
  simpl.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  destruct b as [|] eqn:E.
  - (* case: E: b = true *)
    simpl.
    reflexivity.
  - (* case: E: b = false *)
    simpl.
    reflexivity.
Qed.

(* sub-destruct to enumerate all cases *)
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.




