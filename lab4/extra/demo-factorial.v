Set Implicit Arguments.
Require Import Arith.
Import Nat.

(* From "Formal Reasoning About Programs"

   factorial(n) {
      a = 1;
      while (n > 0) {
         a = a * n;
         n = n - 1;
      }
      return a; 
   }
*)

Inductive state : Set :=
  InLoop: nat -> nat -> state      (* n, a *)
| Exit:   nat -> state.          (* a *)

Inductive init n0 : state -> Prop :=
  start : init n0 (InLoop n0 1).

Inductive step : state -> state -> Prop :=
  iter : forall n a, 0 < n -> 
    step (InLoop n a) (InLoop (n - 1) (a * n))
| stop : forall a, 
    step (InLoop 0 a) (Exit a).


(*
 * Specification -- program returns `fact n0`
 *  (where n0 is the input, i.e. initial value of n)
 *)
Definition spec n0 s :=
  match s with
    Exit a => a = fact n0
  | _ => True
  end.

Print fact.  (* `fact` is defined in the Arith library *)


(* General Definition *)
Section ReflexiveTransitiveClosureDef.

  Variable D : Set.
  Variable R : D -> D -> Prop.

  Inductive tc : D -> D -> Prop :=
    tc_refl : forall s, tc s s
  | tc_step : forall s u t, R s u -> tc u t -> tc s t.

End ReflexiveTransitiveClosureDef.
(* - Notice: from this point on, D and R become *arguments* of tc.
             D, however, is implicit. *)
Check tc.
Print Implicit tc.


Theorem spec_holds n0 s0 s :
  init n0 s0 -> tc step s0 s -> spec n0 s.
Proof.
  intros Init Reach.
  induction Reach.
  - destruct Init.
    simpl. trivial.
  - apply IHReach.
                      (* stuck. :( *)
Abort.  (* well, this didn't work. *)

(*
 * Invariant -- supposed to hold for all reachable states.
 *)
Definition inv n0 s :=
  match s with
    InLoop n a => a * fact n = fact n0
  | Exit a => a = fact n0
  end.

(* Note that this is strictly stronger than spec_holds. *)
Lemma inv_inv n0 s0 s : 
    init n0 s0 -> tc step s0 s -> inv n0 s.
Proof.
  intros Init Reach.
  induction Reach.
  - destruct Init.
    unfold inv.
    firstorder.
  - apply IHReach.
                   (* stuck again! *)
Abort. (* how rude. *)

(* Strengthen the proposition even more to make induction work. *)
Lemma inv_inv' n0 s0 s : 
    inv n0 s0 -> tc step s0 s -> inv n0 s.
Proof.
  intros Inv Reach.
  induction Reach.
  - assumption.
  - apply IHReach.
    destruct H.
    + destruct n.
      * inversion H.     (**) Print Peano.lt.
      * unfold inv. unfold inv in Inv. 
        simpl. rewrite sub_0_r.
        rewrite <- mul_assoc. assumption.
    + unfold inv. unfold inv in Inv.
      rewrite <- Inv. firstorder.
Qed. (* third time's the charm *)

(* Let's try that one again, now it should be easy. *)
Lemma inv_inv n0 s0 s : init n0 s0 -> tc step s0 s -> inv n0 s.
Proof.
  intro Init. apply inv_inv'.
  destruct Init.
  unfold inv.
  firstorder.
Qed.

(* And lastly. *)
Theorem spec_holds n0 s0 s : 
    init n0 s0 -> tc step s0 s -> spec n0 s.
Proof.
  intros.
  enough (inv n0 s).
  - destruct s.
    + simpl. trivial.
    + simpl. simpl in H1.
      assumption.
  - eapply inv_inv with s0.  (* `with` fills missing holes *)
    + eassumption.
    + assumption.
Qed.




