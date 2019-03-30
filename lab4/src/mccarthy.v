Set Implicit Arguments.
Require Import List.
Import ListNotations.

Require Import Omega.  (* also makes firstorder more powerful! *)

(*
 * M:
 * 1	if n > 100 then
 * 2		return n – 10
 * 3	else	n := M(n + 11)
 * 4		n := M(n)
 * 5		return n
 *)

Definition state : Set := nat * list nat.

Inductive step : state -> state -> Prop :=
  step1_hi : forall n x xs, n > 100 -> step (1, n :: x :: xs) (x, (n - 10) :: xs)
| step1_lo : forall n xs, n <= 100 -> step (1, n :: xs) (1, (n + 11) :: 4 :: xs)
| step4 : forall n xs, step (4, n :: xs) (1, n :: 5 :: xs)
| step5 : forall n x xs, step (5, n :: x :: xs) (x, n :: xs).

(* = First Invariant = *)
Definition inv1 s :=
  match s with
    (i, n :: xs) => i = 1 \/ i = 4 \/ In 4 xs \/ n >= 91
  | _ => False
  end.

(* = Second Invariant = *)
Definition inv2 (s : state) :=
  match s with
    (i, n :: xs) => forall a, In a xs -> In a [0; 4; 5]
  | _ => False
  end.

(* auxiliary: a simple recursive function that 
   counts occurrences of 4 in a list *)
Fixpoint cnt4 l :=
  match l with
      [] => 0
  | 4 :: xs => 1 + cnt4 xs
  | _ :: xs => cnt4 xs
  end.

(* = Third Invariant = *)
Definition inv3 (s : state) :=
  match s with
    (i, n :: xs) => (i = 1 \/ i = 4) /\ n <= (cnt4 xs) * 10 + 101 \/
                   (i = 0 \/ i = 5) /\ n <= (cnt4 xs) * 10 + 91
  | _ => False
  end.


Section ReflexiveTransitiveClosureDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, R s u -> tc u t -> tc s t.

End ReflexiveTransitiveClosureDef.

(*
 * The invariant property is expressed over all reachable states.
 *)
Definition inv123 s := inv1 s /\ inv2 s /\ inv3 s.

(* Hint 1: try to prove each invariant separately, as lemmas, before
           combining them to prove inv123_tc.
   Hint 2: inv3 depends on inv2!
*)
                                              
Lemma inv123_tc s1 s2 : inv123 s1 -> tc step s1 s2 -> inv123 s2.


Theorem mccarthy91 n n' : n <= 101 ->
                          tc step (1, [n; 0]) (0, [n']) ->
                          n' = 91.

  