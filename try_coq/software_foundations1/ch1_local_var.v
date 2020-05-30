Inductive mynat : Type :=
  | stop : mynat
  | tick : mynat -> mynat
.

Check mynat.

Check (tick (tick (tick stop))).

Let three:mynat := tick (tick (tick stop)).

Check 

Inductive named_number : Type :=
  | zero : mynat 
  | one : mynat.
.