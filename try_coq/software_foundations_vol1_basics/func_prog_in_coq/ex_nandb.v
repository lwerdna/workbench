Inductive bool : Type :=
  | true
  | false.

Definition negb (b1:bool) : bool :=
  match b1 with
  | true => false
  | false => true
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => negb b2
  end.

Example test_nandb1: (nandb true false) = true.
simpl.
reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
simpl.
reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
simpl.
reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
simpl.
reflexivity.
Qed.
