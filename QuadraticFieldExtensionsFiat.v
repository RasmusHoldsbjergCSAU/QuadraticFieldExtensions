Require Import QuadraticFieldExtensions.
Require Import Crypto.Algebra.Hierarchy.
Require Import ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import List.
Require Import Lia.
From Coqprime Require Import GZnZ.
From Coq Require Import Field.
From Coqprime Require Import Pmod.

Check field.

Check Build_field.

Print field.

Variable p: Z.
Hypothesis p_prime: prime p.
Hypothesis p_odd: 2 < p. 
Hypothesis p_mod3: p mod 4 =? 3 = true.


Definition Fps := (FFp2 p p_prime p_odd p_mod3).

Add Field FFp2: (FFp2 p p_prime p_odd p_mod3).
Add Field Fp : (FZpZ p p_prime).

Instance Fp2 : field (T := (znz p * znz p)%type) (eq := @eq (znz p * znz p)) (zero := zerop2 p) (one := onep2 p)
               (opp := oppp2 p) (add := addp2 p) (sub := subp2 p) (mul := mulp2 p) (inv := invp2 p) (div := divp2 p).
Proof.
    repeat split; try apply (Finv_l (Fps)); try (symmetry; apply (F_1_neq_0 (Fps))); try apply (_ (Fps));
    try auto; try rewrite p_mod3; intros; try apply Fp2irr; simpl; try field; try (case x; intros;
    apply Fp2irr; simpl; try field); try (intros; subst; reflexivity); try (unfold not; intros H; apply (F_1_neq_0 Fps); auto).
Qed.

Check Fp2.

