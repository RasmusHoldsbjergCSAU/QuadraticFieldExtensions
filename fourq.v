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
Require Import FieldsUtil.
Require Import SquareTest.

Section FourQ.
    Definition p := (2^127 - 1)%Z.
    (*Hypothesis p_value: p = 2^127 - 1.*)
    Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).

    Lemma p_gt_2: 2 < p.
    Proof. unfold p; simpl; auto with zarith. Qed.

    Lemma p_odd: Z.odd (Z.of_nat (length (all_Fp2 p p_gt_2))) = true.
    Proof.
        rewrite all_Fp2_length, Nat2Z.inj_abs_nat; auto.
    Qed.

    Lemma p_prime: (prime p).
    Proof. Admitted.
        (* assert (p = Mp 127) as Hmp by reflexivity; rewrite Hmp; 
        exact (LucasTest 127 (refl_equal _)). 
    Qed. *)


    Lemma p_mod: p mod 4 =? 3 = true.
    Proof. apply Z.eqb_eq; auto with zarith. Qed.

    Lemma mone_non_res: Quad_non_res p = (-1 zmod p).
    Proof. unfold Quad_non_res; rewrite p_mod; reflexivity. Qed.

    Definition F := FFp2 p p_prime p_gt_2 p_mod.
    Definition a := (-1 zmod p, zero p).
    Definition d := ( 4205857648805777768770 zmod p,
    125317048443780598345676279555970305165 zmod p).
    Notation Fset := (znz p * znz p)%type.

    Definition d' := ( 4205857648805777768770 zmod (2^127 - 1),
    125317048443780598345676279555970305165 zmod (2^127 - 1)).

    Add Field FFp2 : (FFp2 p p_prime p_gt_2 p_mod).
    Add Field Fp : (FZpZ p p_prime).

    Lemma nonzero_a: a <> zerop2 p.
    Proof.
        rewrite Zerop2_iff; intros contra; destruct contra as [H1 _].  pose proof p_gt_2 as p_odd.
        apply Zerop_iff in H1; simpl in H1; try auto with zarith. assert (0 = 0 mod p) as H2 by auto with zarith. rewrite H2 in H1.
        rewrite <- Z_mod_plus_full with (-1) (1) (p) in H1. simpl in H1;
        do 2 rewrite Zmod_small in H1; auto with zarith.
    Qed.

    Print Rings.

    Lemma square_a: exists sqrt_a, mulp2 p sqrt_a sqrt_a = a.
    Proof. exists (zero p,one p). apply Fp2irr; (try rewrite mone_non_res; simpl; field). Qed.

    Lemma nonzero_d: d <> zerop2 p.
    Proof.
        rewrite Zerop2_iff. intros contra. destruct contra as [H1 _]. pose proof p_gt_2.
        apply Zerop_iff in H1; try auto. simpl in H1. rewrite Zmod_small in H1; try auto with zarith.
    Qed.

    Lemma criterion_exponent: (p * p - 1) / 2 = 14474011154664524427946373126085988481488606899744601273200510697273257099264.
    Proof.
        auto.    
    Qed.

    Lemma d_power_val : @RepeatedSquaring.pow_pos (znz p * znz p) (mulp2 p) (d) (14474011154664524427946373126085988481488606899744601273200510697273257099264%positive) =
        ({|
        val := 170141183460469231731687303715884105726;
        inZnZ := modz 170141183460469231731687303715884105727
                170141183460469231731687303715884105726 |},
        {|
        val := 0;
        inZnZ := modz 170141183460469231731687303715884105727 0 |}).
    Proof. Admitted. (* auto. Qed. *)


    Lemma nonsquare_d : forall x, mulp2 p x x <> d.
    Proof.
        intros x contra.
        apply (@square_criterion Fset (zerop2 p) (onep2 p) (addp2 p) (mulp2 p) (subp2 p)
            (oppp2 p) (divp2 p) (invp2 p) (FFp2 p p_prime p_gt_2 p_mod) (all_Fp2 p p_gt_2)
            (Fp2_list_unique p p_gt_2) (in_all_Fp2 p p_gt_2) (eq_dec_Fp2 p) (p_odd) d).
            - apply Fstar_list_elems, nonzero_d.
            - rewrite all_Fp2_length.
            assert (H' : (Z.of_nat (Z.abs_nat (p * p))) - 1 = p * p - 1) by (unfold p; lia);
            rewrite H', criterion_exponent, rep_square_criterion.
                + rewrite d_power_val; intros contra2; inversion contra2.
                + apply Fstar_list_elems; intros contra2; inversion contra2 as [H1];
                do 2 rewrite Zmod_small in H1; try (rewrite p_value; lia);
                discriminate.
            - exists x; simpl; rewrite <- contra; field.
    Qed. 

        
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
    Defined.

    Definition Feq := (@eq (znz p * znz p)).

    Lemma char_ge_3 : @Ring.char_ge (znz p * znz p)%type Feq (zerop2 p) (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p) 3.
    Proof. apply (@Char_Fp2_geq_p p p_prime); unfold p; lia. Qed. 


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
        (eq_dec_Fp2 p)
        a
        d
        nonzero_a
        square_a
        nonsquare_d.

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
End FourQ.