Set Implicit Arguments.
Require Import Arith.

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

  Definition state : Set := nat * nat.     (* (n, a) *)

  Inductive init n0 : state -> Prop :=
    start : init n0 (n0, 1).
  
  Inductive step : state -> state -> Prop :=
    step0 : forall n a, n > 0 -> step (n, a) (n - 1, a * n).


  (*
   * Specification -- program returns `fact n0`
   *  (where n0 is the input, i.e. initial value of n)
   *)
  Definition spec n0 s :=
    match s with
      (0, a) => a = fact n0
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

  
  Theorem spec_holds n0 s0 s : init n0 s0 -> tc step s0 s -> spec n0 s.
  Proof.
    intros Init Reach.
    induction Reach.
    - destruct Init.
      simpl. destruct n0.
      + simpl. reflexivity.
      + constructor.
    -     (* stuck. :( *)
  Abort.  (* well, this didn't work. *)

  (*
   * Invariant -- supposed to hold for all reachable states.
   *)
  Definition inv n0 s :=
    match s with
      (n, a) => a * fact n = fact n0
    end.

  (* Note that this is strictly stronger than spec_holds. *)
  Lemma inv_inv n0 s0 s : init n0 s0 -> tc step s0 s -> inv n0 s.
  Proof.
    intros Init Reach.
    induction Reach.
    - (* initial state *)
      destruct Init.
      unfold inv.
      firstorder.
    -    (* stuck again! *)
  Abort. (* how rude. *)

  (* Strengthen the proposition even more to make induction work. *)
  Lemma inv_inv' n0 s0 s : inv n0 s0 -> tc step s0 s -> inv n0 s.
  Proof.
    intros Inv Reach.
    induction Reach.
    - assumption.
    - apply IHReach.
      destruct H.
      destruct n.
      + inversion H.
      + simpl. unfold inv in Inv.
        rewrite Nat.sub_0_r.
        rewrite <- Nat.mul_assoc.
        assumption.
  Qed. (* third time's the charm *)

  (* Let's try that one again, now it should be easy. *)
  Lemma inv_inv n0 s0 s : init n0 s0 -> tc step s0 s -> inv n0 s.
  Proof.
    intro Init; apply inv_inv'.
    destruct Init.
    unfold inv.
    firstorder.
  Qed.

  (* And lastly. *)
  Theorem spec_holds n0 s0 s : init n0 s0 -> tc step s0 s -> spec n0 s.
  Proof.
    intros.
    enough (inv n0 s).
    - destruct s.
      unfold spec.
      destruct n, H1.
      + simpl. firstorder.
      + constructor.
    - eapply inv_inv.
      eassumption.
      assumption.
  Qed.
  