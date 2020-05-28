Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.

Proof.
  intros n.
  destruct n as [|] eqn:E.
  - (* when n = 0 *)
    reflexivity.
  - (* when n = S n' *)
    simpl.
    reflexivity.
  
Qed.