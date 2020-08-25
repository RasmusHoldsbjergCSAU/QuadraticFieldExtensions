Require Import QuadraticFieldExtensions.
Require Import ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import List.
Require Import Lia.
Require Import Field.
From Coqprime Require Import SMain.
From Coqprime Require Import Euler.
From Coqprime Require Import UList.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Zp.
From Coqprime Require Import Pmod.
Require Import Zpow_facts.
Require Import Znat.
From Coqprime Require Import LucasLehmer.


Variable p: Z.
Hypothesis p_value: p = 2^127 - 1.
Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).

Lemma p_gt_2: 2 < p.
Proof. rewrite p_value; simpl; auto with zarith. Qed.

Lemma p_prime: (prime p).
Proof.
    assert (p = Mp 127) as Hmp by (apply p_value; reflexivity); rewrite Hmp. 
    exact (LucasTest 127 (refl_equal _)).
Qed.

Lemma p_mod: p mod 4 =? 3 = true.
Proof. apply Z.eqb_eq; rewrite p_value; auto with zarith. Qed.

Check FFp2 p p_prime p_gt_2 p_mod.

Add Field FFp2: (FFp2 p p_prime p_gt_2 p_mod).

Notation "'d'" := ( 4205857648805777768770 zmod p,
                    125317048443780598345676279555970305165 zmod p) (at level 100).
Check FFp2.
Check addp2.

Notation "'K'" := (znz p * znz p)%type (at level 100).
Notation "1K" := (onep2 p).
Notation "0K" := (zerop2 p).
Notation "x +K y" := (addp2 p x y) (at level 100).
Notation "x -K y" := (subp2 p x y) (at level 100).
Notation "x *K y" := (mulp2 p x y) (at level 90).
Notation "x /K y" := (divp2 p x y) (at level 90).
Notation "-K x" := (oppp2 p x) (at level 100).
Check K.

Check (d -K d).

Definition on_curve: -K x *K x +K y *K y = onep2 p +K d *K x *K x *K y *K y. 

Structure FourQ: Set :=
    mkfourq{
        v1 : K;
        v2 : K;
        H : (-K v1 *K v1 +K v2 *K v2) = (onep2 p -K d *K v1 *K v1 *K v2 *K v2);
        }.

Lemma sum_on_curve: forall (p1, p2 : FourQ),
    let s1 = (p1.v1 *K p2.v2 +K p1.v2 *K p2.v1) /K (onep2 p +K p1.v1 *K p1.v2 *K p2.v1 *K p2.v2) in (
        let s2 = (p1.v2 *K p2.v2 +K p1.v1 *K p2.v1) /K (onep2 p -K p1.v1 *K p1.v2 *K p2.v1 *K p2.v2) in(

        )
    )

(*  https://eprint.iacr.org/2008/013.pdf
    https://eprint.iacr.org/2015/565.pdf*)