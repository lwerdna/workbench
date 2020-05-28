Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition ltb (n m : nat) : bool := leb (S n) m.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
simpl.
reflexivity.
Qed.

Example test_ltb2: (ltb 2 4) = true.
simpl.
reflexivity.
Qed.

Example test_ltb3: (ltb 4 2) = false.
simpl.
reflexivity.
Qed.