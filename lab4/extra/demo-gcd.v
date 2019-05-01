Set Implicit Arguments.
Require Import Arith.
Import Nat.



  (* Definition of divisibility + some syntactic sugar *)
  Definition divides a b := exists k, a * k = b.
  Notation "( a | b )" := (divides a b).

  Lemma divides_refl : forall n, (n | n).
  Proof.
    exists 1. firstorder.
  Qed.


  Section Gcd.

    Definition state : Set := nat * nat.
  
    Inductive step : state -> state -> Prop :=
      step_a : forall a b, a > b -> step (a, b) (a - b, b)
    | step_b : forall a b, a < b -> step (a, b) (a, b - a).


    Require Import Omega.
  
    Lemma div_inv a b a' b' : step (a, b) (a', b') ->
            forall z,  (z | a) /\ (z | b)  <->  (z | a') /\ (z | b').
    Proof.
      intro H. inversion H.
      - subst. firstorder.
        + exists (x0 - x). rewrite mul_sub_distr_l. firstorder.
        + exists (x0 + x). rewrite mul_add_distr_l. omega.
      - subst. firstorder.
        + exists (x - x0). rewrite mul_sub_distr_l. firstorder. (*   firstorder also works, *)
        + exists (x0 + x). rewrite mul_add_distr_l. firstorder. (* <- when Omega is loaded  *)
    Qed.

  
    Definition is_gcd (a b z : nat) :=
      (z | a) /\ (z | b) /\ forall z', (z' | a) -> (z' | b) -> (z' | z).  


    Lemma gcd_inv a b a' b' : step (a, b) (a', b') ->
                              forall z, is_gcd a b z <-> is_gcd a' b' z.
    Proof.
      intro H. pose (div_inv H).
      firstorder.
      - apply H2; firstorder.
      - apply H2; firstorder.
    Qed.

    (* Lesson learned: *)
    (* `firstorder` is mighty powerful, if you know what *)
    (* assumptions to feed it. *)
  
  End Gcd.
