(* listed, numerated, set type *)
 Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  (* is p is a member of rgb, then primary p is a member of color *)
  | primary (p : rgb).

Check rgb.
Check color.
Check red.
Check black.

(* you don't actually construct a "color" from an "rgb", you let the type system act as an if statement *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  (* you claim to be a primary, send q as argument and see if it is (if q is an rgb) *)
  | primary q => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false (* primary applied to ANY rgb constructor except red *)
  end.
