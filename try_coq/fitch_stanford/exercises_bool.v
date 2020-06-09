(* these solutions use type bool true/false *)

Theorem conjunction_elimination_left : forall a b : bool,
  (andb a b)=true -> a=true.
Proof.
  intros a b.
  intros H1.
  destruct a as [|] eqn:E.
    (* case: a is true *)
    reflexivity.
    (* case: a is false *)
    rewrite <- H1.
    simpl.
    reflexivity.
Qed.

Require Import Bool.

(* http://intrologic.stanford.edu/exercises/exercise_04_01.html *)
Theorem fitch_04_01 : forall p q r: bool,
  p=true /\ q=true /\ (((andb p q)=true) -> r=true) -> r=true.
Proof.
  intros p q r tmp.
  destruct tmp as [p_holds tmp].
  destruct tmp as [q_holds tmp].
  destruct tmp as [pq_implies_r].
  rewrite p_holds. 
  rewrite q_holds.
  simpl.
  reflexivity.
  reflexivity.
Qed.

(* http://intrologic.stanford.edu/exercises/exercise_04_02.html *)
Theorem fitch_04_02 : forall p q : bool,
  (andb p q)=true -> (orb p q)=true.
Proof.
  intros p q.
  intros H.
  apply conjunction_elimination_left in H.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Definition implies (p q:bool) : Prop :=
  match p, q with
  | true, false => False
  | _, _ => True
end.

Lemma modus_ponens : forall p q : bool,
  (implies p q) /\ p=true -> q=true.
Proof.
  intros p q H.
  destruct H.
  destruct q as [|] eqn:q_holds.
  (* q=true *)
  reflexivity.
  (* q=false *)
  rewrite H0 in H.
  simpl in H.
  contradiction.
Qed.

Lemma modus_easy : forall q : bool,
  (implies true q) -> q=true.
Proof.
  intros q H.
  destruct q.
  reflexivity.
  simpl in H.
  contradiction.
Qed.

(* http://intrologic.stanford.edu/exercises/exercise_04_03.html *)
Theorem fitch_04_03 : forall p q r : bool,
  (implies p q) /\ (implies q r) -> (implies p r).
Proof.
  intros p q r H.
  destruct H.
  destruct p as [|] eqn:E.
  apply modus_easy in H.
  rewrite H in H0.
  apply modus_easy in H0.
  rewrite H0.
  reflexivity.
  reflexivity.
Qed.
