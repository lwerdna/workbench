(* two attacks on and elimination from Software Foundations *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  reflexivity.
  rewrite <- H.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem andb_true_elim2_ : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  reflexivity.
  destruct b.
  simpl in H.
  discriminate.
  simpl in H.
  discriminate.
Qed.

(* made up example using color type from Software Foundations *)

Inductive color : Type :=
  | red
  | green
  | blue.
  
Definition johns_favorite_color (c:color) : bool :=
  match c with
  | red => true
  | green => false
  | blue => false
  end.
  
Theorem test_theorem : forall c:color,
  (johns_favorite_color c)=true -> c=red.
Proof.
  intros c.
  intros H.
  destruct c as [r|g|b] eqn:E.
  (* c is red *)
  reflexivity.
  (* c is green *)
  simpl in H.
  discriminate.
  (* c is blue *)
  simpl in H.
  discriminate.
Qed. 

(* modus ponens on bool is an example *)

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

(* tollens *)
Lemma modus_tollens : forall p q : bool,
  (implies p q) /\ q=false -> p=false.
Proof.
  intros p q H.
  destruct H.
  destruct p.
  rewrite H0 in H.
  simpl in H.
  contradiction.
  reflexivity.
Qed.

(* greater than some num *)