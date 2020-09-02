Require Import ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import List.
Require Import Lia.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import QuadraticFieldExtensions.
From Coq Require Import Field.
From Coqprime Require Import SMain.
From Coqprime Require Import Euler.
From Coqprime Require Import UList.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Zp.
From Coqprime Require Import Pmod.
Require Import Zpow_facts.
Require Import Znat.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable.
From Coqprime Require Import LucasLehmer.
Require Import RingsUtil.

Variable p: Z.
Hypothesis p_value: p = 2^127 - 1.
Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).

Lemma p_gt_2: 2 < p.
Proof. rewrite p_value; simpl; auto with zarith. Qed.

Lemma p_prime: (prime p).
Proof. Admitted.
(*     assert (p = Mp 127) as Hmp by (apply p_value; reflexivity); rewrite Hmp. 
    exact (LucasTest 127 (refl_equal _)).
Qed. *)

Lemma p_mod: p mod 4 =? 3 = true.
Proof. apply Z.eqb_eq; rewrite p_value; auto with zarith. Qed.

Lemma mone_non_res: Quad_non_res p = (-1 zmod p).
Proof. unfold Quad_non_res; rewrite p_mod; reflexivity. Qed.

Add Field FFp2: (FFp2 p p_prime p_gt_2 p_mod).
Add Field Fp : (FZpZ p p_prime).

Definition F := FFp2 p p_prime p_gt_2 p_mod.
Definition a := (-1 zmod p, zero p).
Definition d := ( 4205857648805777768770 zmod p,
125317048443780598345676279555970305165 zmod p).

(* Notation sqrt_five := (0 zmod p, 87392807087336976318005368820707244464 zmod p).

Lemma sqrt_five_square: mulp2 p sqrt_five sqrt_five = (5 zmod p, 0 zmod p).
Proof.
     unfold mul. simpl. apply Fp2irr. apply zirr. simpl. rewrite mone_non_res. simpl. repeat rewrite <- Zmult_mod.
Qed.


Lemma p_mod_20: p mod 20 = 7.
Proof.
    rewrite p_value. simpl. auto with zarith.
Qed.
 *)


Lemma nonzero_a: a <> zerop2 p.
Proof.
    rewrite Zerop2_iff; intros contra; destruct contra as [H1 _].  pose proof p_gt_2 as p_odd.
    apply Zerop_iff in H1; simpl in H1; try auto with zarith. assert (0 = 0 mod p) as H2 by auto with zarith.
    rewrite H2, <- Z_mod_plus_full with (-1) (1) (p) in H1. do 2 rewrite Zmod_small in H1; auto with zarith.
Qed.

Lemma square_a: exists sqrt_a, mulp2 p sqrt_a sqrt_a = a.
Proof. exists (zero p,one p). apply Fp2irr; try rewrite mone_non_res; simpl; field. Qed.

Hypothesis nonsquare_d : forall x, mulp2 p x x <> d.

Instance Rp2 : ring (T := (znz p * znz p)%type) (eq := @eq (znz p * znz p)) (zero := zerop2 p) (one := onep2 p)
               (opp := oppp2 p) (add := addp2 p) (sub := subp2 p) (mul := mulp2 p).
Proof.
    apply (@std_to_fiatCrypto_ring (znz p * znz p) (zerop2 p) (onep2 p)
    (addp2 p) (mulp2 p) (subp2 p) (oppp2 p) (F_R (FFp2 p p_prime p_gt_2 p_mod))).
Qed.

Instance Fp2 : field (T := (znz p * znz p)%type) (eq := @eq (znz p * znz p)) (zero := zerop2 p) (one := onep2 p)
               (opp := oppp2 p) (add := addp2 p) (sub := subp2 p) (mul := mulp2 p) (inv := invp2 p) (div := divp2 p).
Proof.
    apply (@std_to_fiatCrypto_field (znz p * znz p) (zerop2 p)
    (onep2 p) (addp2 p) (mulp2 p) (subp2 p) (oppp2 p)
    (divp2 p) (invp2 p) (FFp2 p p_prime p_gt_2 p_mod)).
Qed.

Lemma decidable_Feq : DecidableRel (@eq (znz p * znz p)).
Proof. simpl. intros. case x as [x1 x2], y as [y1 y2]. case x1 as [vx1], x2 as [vx2], y1 as [vy1], y2 as [vy2].
    destruct (Z.eq_dec vx1 vy1); destruct (Z.eq_dec vx2 vy2); try (right; intros contra; inversion contra; contradiction).
    - left. apply Fp2irr; apply zirr; auto with zarith.
Qed.

Definition Feq := (@eq (znz p * znz p)).

Lemma char_ge_3 : @Ring.char_ge (znz p * znz p)%type Feq (zerop2 p) (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p) 3.
Proof. apply (@Char_Fp2_geq_p p p_prime). rewrite p_value. lia. Qed. 


Definition FourQ := @AffineProofs.E.edwards_curve_commutative_group
    (znz p * znz p)
    (@eq (znz p * znz p))
    (zerop2 p)
    (onep2 p)
    (oppp2 p)
    (addp2 p)
    (subp2 p)
    (mulp2 p)
    (invp2 p)
    (divp2 p)
    Fp2
    char_ge_3
    decidable_Feq
    a
    d
    nonzero_a
    square_a
    nonsquare_d.

Check FourQ.

(*
Local Notation point  := (@E.point (znz p * znz p)%type Feq (onep2 p) (addp2 p) (mulp2 p) a d).
Local Notation eq     := (@E.eq (znz p * znz p)%type (@eq (znz p * znz p)) (onep2 p) (addp2 p) (mulp2 p) a d).
Local Notation zero   := (E.zero (nonzero_a := nonzero_a) (Feq_dec := decidable_Feq) (d := d)).
Local Notation add    := (@E.add (znz p * znz p)%type Feq (zerop2 p) (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p) (invp2 p) (divp2 p) Fp2 char_ge_3 decidable_Feq a d nonzero_a square_a nonsquare_d).
Local Notation mul    := (@E.mul (znz p * znz p)%type (@eq (znz p * znz p)%type) (zerop2 p) (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p) (invp2 p) (divp2 p) (Fp2) (decidable_Feq) a d nonzero_a square_a nonsquare_d).
Local Notation coordinates := (@E.coordinates (znz p * znz p)%type Feq (onep2 p) (addp2 p) (mulp2 p) a d).
Local Notation opp := E.opp.

Lemma FourQ_commutative_addition: forall P Q, add P Q = add Q P.
Proof.
    intros. unfold add. simpl. auto. 
*)