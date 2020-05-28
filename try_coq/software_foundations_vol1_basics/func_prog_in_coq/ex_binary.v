Inductive bin : Type :=
  | Z
  | A (n : bin) (* 0 *)
  | B (n : bin) (* 1 *).

Fixpoint incr (m:bin) : bin :=
  (* remember, lsb is leftmost, or outermost *)
  match m with
  | Z => (B Z) (* 0 increments to 1 *)
  | A m' => (B m') (* 0xxx, increments to 1xxx *)
  | B m' => (A (incr m')) (* 1xxx, increments to 0_incr(xxx) *)
  end
.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m' => 2 * (bin_to_nat m') (* 0xxx is 2*xxx *)
  | B m' => 1 + 2 * (bin_to_nat m') (* 1xxx is 1+2*xxx *)
  end
.

(* a unit test is an Example that can be proved with just reflexivity *)
Example test_bin_incr1:
  incr Z = B Z.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2:
  incr (A (A (B Z))) = B (A (B Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3:
  incr (B (B (B Z))) = (A (A (A (B Z)))).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4:
  incr (incr (incr (incr Z))) = (A (A (B Z))).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5:
  incr (incr (incr (incr (incr (incr (incr (incr (incr (incr Z))))))))) = (A (B (A (B Z)))).
Proof. simpl. reflexivity. Qed.

Example test_bin_conv1:
  bin_to_nat Z = 0.
Proof. simpl. reflexivity. Qed.

Example test_bin_conv2:
  bin_to_nat (incr (incr (incr (incr (incr (incr (incr (incr (incr (incr Z)))))))))) = 10.
Proof. simpl. reflexivity. Qed.