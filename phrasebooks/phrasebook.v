  (* enumerated type, bare constructors
   Inductive <name> := <constr1> | <constr2> | ... .
*)
Inductive bool := true | false.
Inductive bool2:Set := true2 | false2. (* "programs" *)
Inductive bool3:Prop := true3 | false3.
Inductive bool4:Type := true4 | false4.

(* parameterized constructors
   Inductive <name> := <constr1>(arg1 arg2 ...: <type_arg>).
*)
Inductive bitfield := Byte(b7 b6 b5 b4 b3 b2 b1 b0: bool) |
                      Nybble(b3 b2 b1 b0: bool) |
                      Bit(b0: bool) .

(* record type *)
Record human :=
MakeHuman {
  age: nat;
  weight: nat;
  gender: bool
}.
Definition John:human := MakeHuman 30 170 false.
Print John.

(* define function
   Definition <fname>: <in_out_type> :=
     fun (type_inp) =>
       ...
*)
Definition negate: bool -> bool :=
  fun (x: bool) =>
    match x with
      false => true
     |true => false
     end.

(* define function (shorthand)
   Definition <fname> <type_in1> <type_in2> ... [: <type_out>] :=
*)
Definition negate'(x:bool) : bool :=
	match x with false => true | true => false end.

(* declare theorems
     Theorem <tname> : <logic>.
     <tactics>
     Qed.
*)
Theorem negate_reverse:
  forall x:bool, negate x = true -> x = false.
    intros x H.
    destruct x.
    discriminate.
    reflexivity.
    Qed.

Print negate_reverse.

(* Console Commands *)

`Show Proof.` put within Proof. ... Qed. to show current proof state
`Check <term>.`
`Compute <term>.`
`Show Existentials.`
`Print <term>.` prints original source
`Locate "="` find what function name operator responds to

`Definition myvar : bool := true.` declare variable

# Scopes

| what             | scope            | decl/def    | looks like       | synonym         |
| ---------------- | ---------------- | ----------- | ---------------- | --------------- |
| axiom            | global (environ) | declaration | `Axiom x:P`      | `Parameter x:P` |
| hypothesis       | local (context)  | declaration | `Hypothesis h:P` | `Variable h:P`  |
| theorems, lemmas | global (environ) | definition  |                  |                 |

* anything to the right of ":" must be a Set, Prop, or Type

# Terminology

**axiom** is a global declaration of type proposition, eg: `Parameter x:P`, or `Axiom x:P`

**hypothesis** is a local declaration of type proposition, eg: `Variable h: P.`  or `Hypothesis h: P`.

**goal** - the proposition that needs to be proved, a pairing of two pieces of information: a local context and a type that is well formed in this context

**solution** a well-formed term in the environment of E and context T

**gallina** is language (that tyou type in) of Coq

format is sequence of:

* declarations
  * name (like a programming language identifier)
  * specification, three types:
    * logical poposition **Prop**
    * mathematical collections **Set**
    * abstract types **Type**
* definitions
* commands

```
asdf
```

# Tactics

local hypothesis with a goal is called a **judgement**

`intros n` "introduce" is a tactic that applies to any judgement whose goal is an implication
version 1: "moves the antecedent of the goal to the list of local hypotheses"
version 2: "moves the variable n from the quantifier in the goal to a context of current assumptions"
version 3: "suppose n is some number..."

`Example` makes a precise claim about the behavior of some function on some particular inputs.

## types

every expression in Coq has a type, describing what sort of thing it computes

`Check O.` gives type of `nat` (zero)
`Check nat.` gives type `Set`
obviously `O` ("Oh") and "nat" are built-in types
`Check gt.` returns a function `nat -> nat -> prop` or `nat -> (nat -> prop)`
specification types: `nat`
abstract types: `Prop` eg `Check Prop.` returns `Type`

an **enumerated type** lists out, or enumerates a finite set of animals, eg:

```
Inductive rgb : Type :=
	| red
	| green
	| blue.
```

the red, green, and blue are constructors in the set rgb


## random commands

`Variable n : nat.`is same as "let n be a natural number"

`Hypothesis Pos_n : (gt n 0).` makes a requirement that greater_than(n, 0), or n is positive

`Reset Declaration.`

## documentation

Reference manual: https://coq.inria.fr/distrib/current/refman/
Gallina language - https://coq.inria.fr/refman/language/gallina-specification-language.html
The best: https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab18
