
(* here's why Inductive is used in type definitions: because definitions can refer to themselves!

nat can be an 0 or it can be an S applied to a nat!
*)

(* don't override built-in nat
Inductive nat : Type :=
  | O
  | S (n : nat). (* where S: nat -> nat *)
*)

(* wtf's S?
nat -> nat *)
Check S.

(* not there's nothing special about O and S *)
Inductive nat' : Type :=
	| stop
	| tick (foo : nat').

Check nat'.

Check (S (S (S (S O)))).

(* pattern matching can match function calls!
	"if the argument n is the product of two S calls then..." *)
Definition minustwo (n : nat) :=
	match n with
		| O => O
		| S O => O
		| S (S k) => k
	end.

(* how to just declare four !? *)

Compute (minustwo (S (S (S (S O))))).

(* definitions that call themselves need to be declared with "Fixpoint" instead of "Definition" *)
Fixpoint evenb (n:nat) : bool :=
	match n with
		| O => true
		| S O => false
		| S (S n') => evenb n'
	end.

(* two argument function *)
 Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

(* two argument function collapsing two arguments of the same type *)
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(* matching on more than one variable ("simultaneous matching") *)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
	match n with
		| O => 1
		| S m => (mult n (factorial m))
	end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Check factorial.

(*
Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
Check ((0 + 1) + 1).
*)

(* equals, bool *)
(* nested matching *)
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

(* less than or equal, bool *)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => 
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
	(leb (S n) m)
.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
