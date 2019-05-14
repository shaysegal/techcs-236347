Require Import Arith.
Import Nat.


Load "./hoare".


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

Definition gt01 n m := if gt_dec n m then 1 else 0.

Notation "[ e1 `*` e2 ]" := (expr_op e1 mul e2).
Notation "[ e1 `-` e2 ]" := (expr_op e1 sub e2).
Notation "[ e1 `>` e2 ]" := (expr_op e1 gt01 e2).

Notation "$ v" := (expr_var v) (at level 7, format "$ v").
Notation "# n" := (expr_num n) (at level 7, format "# n").


Definition factorial_cmd :=
  seq (assign a (#1))
      (while [$n `>` #0]
             (seq (assign a [$a `*` $n])
                  (assign n [$n `-` #1]))).



Module MainProof.

  Definition c := seq (assign a [$a `*` $n])
                      (assign n [$n `-` $1]).

  Definition linv n0 (s : state) := s a * fact (s n) = fact n0.

  (* Control the behavior of `simpl` to allow more unfoldings.            *)
  (*                                                                      *)
  (* This should allow you to simplify a substitution term,               *)
  (*   e.g. subst (fun s => s a + 1 = 2) a [$a `-` #1] s                  *)
  (*        ( in other words, (a + 1 = 2)[a - 1 / a] )                    *)
  (*     simplifies to                                                    *)
  (*        s a - 1 + 1 = 2                                               *)
  Arguments subst P v e /.
  Arguments set s v / z.
  Arguments var_eq_dec !v1 !v2.
  Arguments gt01 n m / : simpl nomatch.

  Lemma factorial_inv n0 : hoare (fun s => linv n0 s /\ s n > 0)
                                 c
                                 (linv n0).
  Proof.
    unfold c. unfold linv. eapply hoare_seq.
    Focus 2. apply hoare_assign.
    simpl.
    eapply hoare_weaken_l.
    Focus 2. apply hoare_assign.
    simpl.
    firstorder.
    destruct (s n) as [|k].
    - inversion H0.
    - simpl.
      rewrite Nat.sub_0_r. rewrite <- Nat.mul_assoc. assumption.
  Qed.


  Lemma factorial_correct n0 : hoare (fun s => s n = n0)
                                     factorial_cmd
                                     (fun s => s a = fact n0).
  Proof.
    econstructor.
    Focus 2.
    { econstructor.
      + intros; eassumption.
      + econstructor. simpl.
        eapply hoare_weaken_l.
        Focus 2.
        * apply factorial_inv.
          
        * firstorder.
          { destruct (s n).
            - firstorder.
            - firstorder.
          }
      + simpl. firstorder. unfold linv in H.
        destruct (s n).
        * rewrite Nat.mul_1_r in H. eassumption.
        * simpl in H0. discriminate.
    }
    Unfocus.
    eapply hoare_weaken_l.
    Focus 2.
    econstructor.
    intros; unfold linv; simpl.
    subst; firstorder.
  Qed.

End MainProof.



