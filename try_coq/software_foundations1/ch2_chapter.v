(* 0 on the left can be simplified
  since:
  
Print sum.
Print "+".

Nat.add = 
fix add (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end
  
  TLDR: this knows (add 0 n) = n
           but not (add n 0) = n
           
  it matches on the first parameter n
  
  (sum O 3) is n=0 non-recursive match
  (sum 3 0) is n=3 recursive match
               = S (sum 2 0)
               = S (S (sum 1 0)
               = S (S (S (sum 0 0)))
               = S (S (S 0))
               = 3
               
   but what if you give a variable k?
   
   (sum 0 k) is n=0 so it can return k without knowing its value
   (sum k 0) is n=k so it cannot return k
   
   why doesn't it match on both n and m so this
   will be defined for 0 on either side? like:
   | 0 _ => m
   | _ 0 => n
   | S p => S (add p m)
          
  
  
  now what about:
  
  (sum O x) is n=0 and return
  
*)

Theorem plus_O_n: forall n:nat,
  n = O + n.
Proof.
  intros n.
  simpl.
  reflexivity.
Abort.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

Proof.
  intros n.
  simpl. (* n+0 cannot be simplified because (add n 0)
          doesn't match the base case! *)
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *) 
    simpl. 
    rewrite <- IHn'. 
    reflexivity. 
   Qed.
   
Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
    Qed.
