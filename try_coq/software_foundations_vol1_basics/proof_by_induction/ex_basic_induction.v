Print "*".

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  (* case n=0
    so goal: (0) * 0 = 0 *)
  simpl.
  reflexivity.
  (* case n = S n'
    so goal: (S n') * 0 = 0 *)
    
  (* this simpl. is crazy
    before: (S n') * 0 = 0
     after: n' * 0 = 0
     
     because mul constructor | S p => m + mul p m
     so really it does
     (S n') * 0 = 0       (with p=n' m=0)
     0 + (mul n' 0)
     (mul n' 0)
  *)
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IH].
  (* case n=0 so goal S (0+m) = 0 + (S m)
    and with 0 on the left, we know add is smart.. *)
  simpl.
  reflexivity.
  (* case n=Sn' so goal S(Sn'+m) = Sn'+Sm *)
  
  (* (S n' + m) becomes S (n' + m) why? 
    because constructor | S p => S (add p m)
    with p=Sn' and m=m *)
  simpl.
  rewrite IH.
  reflexivity. 
Qed.

Print "+".

Lemma plus_n_O: forall n:nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IH].
  reflexivity.
  simpl. (* Sn'+0 to S (n'+0) *)
  rewrite <- IH.
  reflexivity.
Abort.

Print "+".

Lemma Sn_is_1_plus_n: forall n:nat,
  S n = 1 + n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Lemma Sn_is_n_plus_1: forall n:nat,
  S n = n + 1.
Proof.
  intros n.
  induction n as [| n' IH].
  simpl.
  reflexivity.
  simpl.
  rewrite IH.
  reflexivity.
Qed.

(* commutivity of addition *)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IH].
  (* case n=0 so goal 0+m=m+0 *)
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
  (* case n=Sn' so goal Sn'+m = m+Sn' *)
  simpl.
  rewrite -> IH.
  rewrite plus_n_Sm.
  reflexivity.
Qed.
  

Print "+".
Lemma associativity_S : forall a b : nat,
  (S a) + b = (S (a+b)).
Proof.
  intros a b.
  induction a as [| k IH].
  (* base case a=0, simply show it's true *)
  simpl.
  reflexivity.
  (* inductive step
    IH: assume true for a=k
    with IH, prove true for a=(S k) *)
  simpl.
  rewrite <- IH.
  reflexivity. 
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| k IH].
  (* base case n=0 *)
  simpl.
  reflexivity.
  (* inductive step
    IH: assume true for n=k
    with IH, prove true for n=(S k) *)
  rewrite -> associativity_S.
  rewrite IH.
  rewrite <- associativity_S.
  rewrite <- associativity_S.
  reflexivity.
Qed.
