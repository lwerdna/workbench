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

Theorem modus_ponens : forall p q : bool,
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
Theorem modus_tollens : forall p q : bool,
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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Compute leb 6 7.
Compute leb 8 7.

Fixpoint yesman (n:nat) : bool :=
  match n with
    | _ => true
  end.

Lemma never_says_no : forall n : nat,
  (yesman n)=true.
Proof.
  intros n.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Lemma no_succ_leb_O : forall n : nat,
  (leb (S n) O)=false.
Proof.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Lemma only_O_leb_O : forall a : nat,
  (leb a O)=true -> a=O.
Proof.
  intros a H.
  destruct a as [|k].
  reflexivity.
  rewrite no_succ_leb_O in H.
  discriminate.
Qed.



Theorem aaa : forall a b : nat,
  (leb (S a) b)=true -> (leb a b)=true.
Proof.
  intros a b H.
  induction a as [|k IH].
    (* 0 *)
    reflexivity.
    (* Sk *)
    apply IH in H.



Theorem test : forall a b : nat,
  (leb a b)=true -> (leb a (S b))=true.
Proof.
  intros a b H.
  destruct a as [|a'].
  (* a=O *)
  reflexivity.
  destruct a' as [|a''].
  reflexivity.
  simpl.
  (* a=Sa' *)
  simpl.

  simpl.
  simpl in H.
Qed.

Theorem aaa : forall a b : nat,
  (leb (S a) b)=true -> (leb a b)=true.
Proof.
  intros a b H.
  destruct b as [|k].
  (* case b=0 *)
  rewrite no_succ_leb_O in H.
  discriminate.
  (* case b=Sk *)
  simpl in H.
  simpl.
  destruct a.
  reflexivity.





Theorem test : forall x : nat,
  (leb x 5)=true -> (leb x 10)=true.
Proof.
  intros x H.
  destruct x as [|] eqn:E.
  reflexivity.

Qed.







