(* see collatz_weak near the bottom *)

Fixpoint test_even (n : nat): bool :=
  match n with
  | O => true
  | S (S n') => (test_even n')
  | _ => false
  end.

Compute (test_even 8).
Compute (test_even 7).
Compute (test_even 6).
Compute (test_even 5).
Compute (test_even 2).
Compute (test_even 1).
Compute (test_even 0).


(* the problem is that using the "S n" pattern
is the only way I know currently to adjust a
value, subtracting 1, 2, ... - there are not
other tools currently to evade coq's "decreasing
analysis" *)

Fixpoint test_even' (n : nat): bool :=
  match (test_even n) with
  | true => true
  | false => false
  end.
  
Fixpoint add_2 (n : nat) : nat :=
  match n with
  | O => 2
  | S n' => S(S(S n'))
  end.
  
Compute (add_2 2).
Compute (add_2 1).
Compute (add_2 0).

Fixpoint sub_3 (n : nat) : nat :=
  match n with
    | S (S (S n')) => n'
    | _ => O
  end.

Compute (sub_3 5).
Compute (sub_3 4).
Compute (sub_3 3).
Compute (sub_3 2).
Compute (sub_3 1).
Compute (sub_3 0).

Fixpoint sum' (a b:nat) : nat :=
  match a with
    |O => b
    |S a' => S (sum' a' b)
  end.
  
Compute (sum' 3 5).


Fixpoint div_2 (n:nat) : nat :=
  match n with
  | 2 => 1
  | S (S n') => 1 + (div_2 n')
  | _ => 0
  end.

Compute (div_2 6).
Compute (div_2 5).
Compute (div_2 4).
Compute (div_2 3).
Compute (div_2 2).
Compute (div_2 1).
Compute (div_2 0).

Fixpoint collatz_weak (n : nat) : nat :=
  match n with
  | O => O
  | 1 => 1
  | _ =>
    match (test_even n) with
      | true => (collatz_weak (div_2 n))
      | false => (collatz_weak (n + 1))
    end
  end
.

Fixpoint collatz (n : nat) : nat :=
  match (test_even n) with
  | true => (collatz (div_2 n))
  | false => (collatz (3*n*n*n + 1))
  end.

Compute (funky 5).

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match m with
  | O => n
  | S m' => S (plus' n m')
  end.
  
  