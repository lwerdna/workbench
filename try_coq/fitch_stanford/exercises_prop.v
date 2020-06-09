(* these solutions use type Prop True/False *)

Require Import Bool.

(* http://intrologic.stanford.edu/exercises/exercise_04_01.html *)
Theorem fitch_04_01 : forall p q r: Prop,
  p /\ q /\ ((p /\ q) -> r) -> r.
Proof.
  intros p q r tmp.
  destruct tmp as [p_holds tmp].
  destruct tmp as [q_holds H].
  assert (p_and_q : p /\ q).
    { split. assumption. assumption. }
  apply H in p_and_q.
  assumption.
Qed.

(* http://intrologic.stanford.edu/exercises/exercise_04_02.html *)
Theorem fitch_04_02 : forall p q : Prop,
  p /\ q -> p \/ q.
Proof.
  intros p q H.
  destruct H.
  left.
  assumption.
Qed.

(* http://intrologic.stanford.edu/exercises/exercise_04_03.html *)
Theorem fitch_04_03 : forall p q r : Prop,
  ((p->q) /\ (q<->r)) -> (p->r).
Proof.
  intros p q r H.
  destruct H.
  intros p_holds.
  apply H in p_holds as q_holds.
  apply H0 in q_holds as r_holds.
  assumption.
Qed.
