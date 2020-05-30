(* Example, Theorem, Lemma, Fact, Remark all mean the same thing to COQ, use what you want *)

(* 0 + n = n *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
	(* each of these three is a tactic *)
	intros n. simpl. reflexivity.
Qed.

(*
forall n:nat, 0+n = n

intros n
"suppose n is some number"
move n from the quantifier in the goal to a context of current assumptions

0+n = n

simplify
n = n

reflexivity
(equality is checked)
no more subgoals

qed
done
*)

(* adding 1 is the same as the successor *) 
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
  
(* multiplying a natural by 0 always yields 0 *)
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
