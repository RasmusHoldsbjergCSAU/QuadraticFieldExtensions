Require Import ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import List.
Require Import Lia.
Require Import Field.
From Coqprime Require Import Euler.
From Coqprime Require Import UList.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Zp.
Require Import Zpow_facts.
Require Import Znat. 

Section Fp2.

Variable p: Z.
Hypothesis p_prime: prime p.
Hypothesis p_odd: 2 < p.

Notation "x +p y" := (add p x y) (at level 100).
Notation "x *p y" := (mul p x y) (at level 90).
Notation "x -p y" := (sub p x y) (at level 100).
Notation "x /p y" := (div p x y) (at level 90).

Definition Quad_non_res: znz p :=
if (p mod 4 =? 3) then mkznz p ((-1) mod p) (modz p (-1))
  else ( if (p mod 8 =? 3) then mkznz p (2 mod p) (modz p 2)
    else mkznz p ((-2) mod p) (modz p (-2)) ).

(*
  | true => mkznz p ((-1) mod p) (modz p (-1))
  | false =>
  match (p mod 8 =? 3) with
    | true => mkznz p (2 mod p) (modz p 2)
    | false => mkznz p ((-2) mod p) (modz p (-2))
  end
end.
*) 


Notation "\beta" := Quad_non_res.

Ltac discriminate_incongruence H:= repeat
      (try (rewrite Zmod_small, Zmod_small in H; auto with zarith);
      rewrite <- Z_mod_plus_full with (b :=1) in H).

Definition Quad_nres_not_zero:
\beta <> zero p.
Proof.
  unfold Quad_non_res, not; intros H. destruct (p mod 4 =? 3).
  - inversion H as [H1]; discriminate_incongruence H1.
  - destruct (p mod 8 =? 3) eqn:case2; inversion H as [H1]; discriminate_incongruence H1.
Qed.


Lemma minus_one_odd_power: forall x,
   0 <= x -> (-1)^(2*x + 1) = -1.
Proof.
  intros x H. pose proof (Z2Nat.id x H) as Hn; symmetry in Hn.
  remember (Z.to_nat x) as x' eqn:Hx; destruct Hx; generalize dependent x; induction (x') as [|x'' IHx''].
  - intros x H H0; simpl in H0; rewrite H0; auto with zarith.
  - intros x H H0. rewrite Nat2Z.inj_succ in H0. assert ((-1)^(2 * (x - 1) + 1) = -1) as H'. apply IHx''. omega.
    + assert (Z.succ (x - 1)= x); auto with zarith.
    + assert (2 * x + 1 = (2 * (x - 1) + 1) + 2) as H2; auto with zarith. try omega.
      rewrite H2. rewrite Zpower_exp; try omega; rewrite H'; auto with zarith.
  Qed.
      


Lemma beta_is_non_res:
~(exists x, (x *p x) = \beta).
Proof.
  intros contra. destruct (p mod 4 =? 3) eqn:case.
  (* Case p mod 4 = 3*)
  - unfold Quad_non_res in contra; rewrite case in contra; destruct contra as [x H]. inversion H as [H1].
    assert ((val p x)^(phi p) mod p = 1). apply phi_power_is_1. auto with zarith.
    apply rel_prime_div with (val p x * val p x).
    apply rel_prime_sym, prime_rel_prime. apply p_prime. intros contra. apply Zdivide_mod in contra. rewrite contra in H1.
    rewrite <- Zmod_0_l with (p) in H1. symmetry in H1. discriminate_incongruence H1.
    auto with zarith.
    apply Z.eqb_eq in case.
    assert (p = 4 * (p / 4) + 3) as H2. rewrite <- case. apply Z_div_mod_eq; auto with zarith.
    apply (f_equal (fun y => y - 1)) in H2. remember (2 * (p / 4) + 1) as m eqn:Hm2.
    assert (p - 1 = 2 * m) as Hm; auto with zarith.
    apply (f_equal (fun y => y^m mod p)) in H1. rewrite <- Zpower_mod in H1; try omega. rewrite <- Zpower_mod in H1; try omega.
    assert (phi p = p - 1) as H3. apply prime_phi_n_minus_1; apply p_prime.
    assert ((val p x * val p x)^m = (val p x) ^ (phi p)) as H4. rewrite H3; rewrite Hm.
    assert (2 * m = m + m); auto with zarith.
    rewrite H4. rewrite Zpower_exp; try auto with zarith; apply Zmult_power; auto with zarith.
    rewrite <- H4 in H0; rewrite H0 in H1.
    assert ((-1)^m = -1) as H5. rewrite Hm2; apply minus_one_odd_power; omega.
    rewrite H5 in H1. rewrite <- Z_mod_plus_full with (-1) (1) (p) in H1.
    rewrite Zmod_small in H1; try auto with zarith.
  - Admitted.
    


Structure Fp2: Set:=
  mkFp2 { v1: znz p;
          v2: znz p}.

Theorem Fp2irr : forall x1 x2 y1 y2,
  x1 = y1 -> x2 = y2 -> mkFp2 x1 x2 = mkFp2 y1 y2.
Proof. intros x1 x2 y1 y2 H1 H2; subst x1 x2; reflexivity. Qed. 

(* Defining Ring Structure of Fp2 *)

Definition zerop2 := mkFp2 (zero p) (zero p).

Definition onep2 := mkFp2 (one p) (zero p).

Definition addp2 x1 x2 :=
  mkFp2 ( v1 x1 +p v1 x2 ) (v2 x1 +p v2 x2).

Definition subp2 x1 x2 :=
  mkFp2 (v1 x1 -p v1 x2) (v2 x1 -p v2 x2).

Definition mulp2 x1 x2 :=
  mkFp2 (v1 x1 *p v1 x2 +p \beta *p v2 x1 *p v2 x2)
        (v1 x1 *p v2 x2 +p v2 x1 *p v1 x2).
  
Definition oppp2 x := mkFp2 (opp p (v1 x)) (opp p (v2 x)).

Add Field Fp : (FZpZ p p_prime).

Definition RFp2: ring_theory zerop2
  onep2 addp2 mulp2 subp2 oppp2 (@eq Fp2).
Proof.
  split;
  intros; case x; intros; refine (Fp2irr _ _ _ _ _ _);
  unfold zerop2, onep2, mulp2, oppp2, addp2, subp2;
  simpl; field.
Qed.

Definition Zerop2_iff: forall x,
  x = zerop2 <-> ( v1 x = zero p /\ v2 x = zero p ).
Proof.
  intros [x1 x2].  split.
  - intros H; inversion H; split; reflexivity.
  - intros H; simpl in H; destruct H as [H1 H2]; rewrite H1, H2; reflexivity.
Qed.

Definition Zerop_iff: forall x,
  x = zero p <-> val p x = 0.
intros.
  split.
  - intros H; destruct x as [xval]; inversion H as [H1]; simpl.
    rewrite Zmod_small in H1. apply H1. auto with zarith.
  - intros H; destruct x as [xval]; refine (zirr p _ _ _ _ _); simpl in H; rewrite H; auto with zarith.
  Qed.

Definition ZpZ_integral_domain: forall x y,
  x <> zero p -> y <> zero p -> (x *p y) <> zero p.
Proof.
  intros x y Hx Hy. assert ((x *p (inv p x)) = one p).
  field; apply Hx.
  intros contra. assert ((one p *p one p) = zero p).
  assert ((x *p y *p inv p x *p inv p y) = zero p). rewrite contra; field; split; assumption.
  rewrite <- H0; field; split; assumption.
  apply (FZpZ p p_prime); rewrite <- H0; field.
Qed.

(* Definining additional field structure *)

Definition invp2 x :=
if ((val p (v1 x)) =? 0) then mkFp2 (zero p) (inv p (v2 x *p \beta))
  else
     mkFp2 ( one p /p v1 x +p ( (v2 x *p v2 x *p \beta /p (v1 x *p v1 x)) *p inv p (v1 x -p ( v2 x *p v2 x *p \beta /p v1 x)) ) )
           ( opp p ((v2 x /p v1 x) /p ( v1 x -p v2 x *p v2 x *p \beta /p v1 x ))).

Definition divp2 x1 x2 := mulp2 x1 (invp2 x2).

Definition FFp2: field_theory zerop2 onep2 addp2 mulp2
  subp2 oppp2 divp2 invp2 (@eq Fp2).
Proof.
  split.
  - apply RFp2.
  - intros H; injection H; intros H'; discriminate_incongruence H'.
  - intros; reflexivity.
  - intros [x1 x2] H. unfold invp2, mulp2, onep2. simpl. destruct (val p x1 =? 0) eqn:eq1; simpl.
    (*Case : x1 is zero*)
    + apply Z.eqb_eq in eq1; refine (Fp2irr _ _ _ _ _ _). field; split.
      * apply Quad_nres_not_zero.
      * intros contra; apply H. rewrite Zerop2_iff, Zerop_iff; auto.
      * apply Zerop_iff in eq1. rewrite eq1. field.
        split. apply Quad_nres_not_zero.
        intros contra; rewrite eq1 in H; rewrite contra in H; contradiction.
    (* Case : x1 is not zero *)
    + apply Z.eqb_neq in eq1; refine (Fp2irr _ _ _ _ _ _); simpl. field. split.
      * intros H1; apply Zerop_iff in H1; contradiction.
      * destruct (val p x2 =? 0) eqn:eq2.
          (* case x2 is zero *)
          apply Z.eqb_eq in eq2; apply Zerop_iff in eq2; rewrite eq2.
          assert ((x1 *p x1 -p (zero p *p zero p) *p \beta) = (x1 *p x1)) as H0. field. rewrite H0.
          apply ZpZ_integral_domain; intros contra; apply Zerop_iff in contra; contradiction.
          (* case x2 is not zero *)
          intros contra.
          apply (f_equal (fun x => (x +p x2 *p x2 *p \beta) /p (x2 *p x2))) in contra.
          field_simplify in contra; try (apply Z.eqb_neq in eq2; apply Zerop_iff in contra; contradiction).
          apply beta_is_non_res; exists (x1 /p x2); rewrite <- contra;
          field; intros contra2; apply Zerop_iff in contra2; apply Z.eqb_neq in eq2; auto.
      * field. split. intros contra; apply Zerop_iff in contra; contradiction.
        destruct (val p x2 =? 0) eqn:eq2.
          (* case x2 is zero *)
          apply Z.eqb_eq in eq2; apply Zerop_iff in eq2; rewrite eq2.
          assert ((x1 *p x1 -p (zero p *p zero p) *p \beta) = (x1 *p x1)) as H0. field. rewrite H0.
          apply ZpZ_integral_domain; intros contra; apply Zerop_iff in contra; contradiction.
          (* case x2 is not zero *)
          intros contra.
          apply (f_equal (fun x => (x +p x2 *p x2 *p \beta) /p (x2 *p x2))) in contra.
          field_simplify in contra; try (apply Z.eqb_neq in eq2; apply Zerop_iff in contra; contradiction).
          apply beta_is_non_res; exists (x1 /p x2); rewrite <- contra;
          field; intros contra2; apply Zerop_iff in contra2; apply Z.eqb_neq in eq2; auto.
Qed.


