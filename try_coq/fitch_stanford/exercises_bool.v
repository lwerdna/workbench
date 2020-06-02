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
