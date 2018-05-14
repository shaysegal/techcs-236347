Require Import Arith.
Require Import Omega.  
Import Nat.


Load hoare.


(*
euclid(a, b):
  while a != b do
    if a > b then
      a := a - b
    else
      b := b - a
 *)

Definition gt01 n m := if gt_dec n m then 1 else 0.
Definition ne01 n m := if eq_dec n m then 0 else 1.

Notation "[ e1 `-` e2 ]" := (expr_op e1 sub e2).
Notation "[ e1 `>` e2 ]" := (expr_op e1 gt01 e2).
Notation "[ e1 `!=` e2 ]" := (expr_op e1 ne01 e2).


Definition euclid_cmd :=
  while [expr_var a `!=` expr_var b]
        (if_then_else [expr_var a `>` expr_var b]
                      (assign a [expr_var a `-` expr_var b])
                      (assign b [expr_var b `-` expr_var a])).


(* Definition of divisibility + some syntactic sugar *)
Definition divides a b := exists k, a * k = b.
Notation "( a | b )" := (divides a b).


Module MainProof.

  Definition c := if_then_else [expr_var a `>` expr_var b]
                               (assign a [expr_var a `-` expr_var b])
                               (assign b [expr_var b `-` expr_var a]).

  Definition linv a0 b0 :=
    fun s => forall z, (z | a0) /\ (z | b0) <-> (z | s a) /\ (z | s b).

  (* Control the behavior of `simpl` to allow more unfoldings. *)
  Arguments subst P v e /.
  Arguments set s v / z.
  Arguments var_eq_dec !v1 !v2.
  Arguments gt01 n m / : simpl nomatch.
  Arguments ne01 n m / : simpl nomatch.

  Lemma gt0_le x y : gt01 x y = 0 <-> x <= y.  Admitted.
  Lemma gt1_gt x y : gt01 x y <> 0 <-> x > y.  Admitted.
  Lemma div_sub a b z : (z | a) -> (z | b) -> (z | a - b).  Admitted.
  Lemma sub_div1 a b z : a >= b -> (z | a) -> (z | a - b) -> (z | b).  Admitted.
  Lemma sub_div2 a b z : a >= b -> (z | b) -> (z | a - b) -> (z | a).  Admitted.

  Lemma warm_up a0 b0 : hoare (fun s => s a = a0 /\ s b = b0)
                              (assign a [expr_var a `-` expr_var b])
                              (fun s => s a = a0 - b0).
  (* Hint 1: use hoare_weaken_l (from hoare.v).
   * Hint 2: don't forget that you can switch subgoals with Focus <num>. 
   *)
  
  Lemma euclid_inv a0 b0 : hoare (fun s => linv a0 b0 s /\ s a <> s b)
                                 c
                                 (linv a0 b0).

  Theorem euclid_post a0 b0 : hoare (fun s => s a = a0 /\ s b = b0)
                                    euclid_cmd
                                    (fun s => forall z, (z | a0) /\ (z | b0) <-> (z | s a)).

    
End MainProof.
