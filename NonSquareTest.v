Require Import ZArith Znumtheory.
Require Import List.
Require Import Lia.
Require Import QuadraticFieldExtensions.
From Coq Require Import Field.
From Coqprime Require Import Pmod.
Require Import Coqprime.PrimalityTest.FGroup.
From Coqprime Require Import LucasLehmer.

Variable p : Z.
Hypothesis p_value : p = 2^127 - 1.

Lemma p_gt_2: 2 < p.
Proof. rewrite p_value; simpl; auto with zarith. Qed.

Lemma p_prime: (prime p).
Proof. Admitted.
(*     assert (p = Mp 127) as Hmp by (apply p_value; reflexivity); rewrite Hmp. 
    exact (LucasTest 127 (refl_equal _)).
Qed. *)

Lemma p_mod: p mod 4 =? 3 = true.
Proof. apply Z.eqb_eq; rewrite p_value; auto with zarith. Qed.

Add Field Fp2 : FFp2 p 

Check mkGroup.