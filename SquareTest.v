Require Import ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import List.
Require Import Lia.
Require Import Permutation.
Require Import Coq.Lists.List.
From Coq Require Import Field.
From Coqprime Require Import Euler.
From Coqprime Require Import UList.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Zp.
From Coqprime Require Import Pmod.
Require Import Zpow_facts.
Require Import Znat.
Require Import Coqprime.PrimalityTest.IGroup.
Require Import Coqprime.PrimalityTest.FGroup.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.Hierarchy.
Require Import Coqprime.PrimalityTest.EGroup.
Require Import FieldsUtil.
Require Import UList.
Require Import RepeatedSquaring.

Section Squaretest.
  Context {F: Set}
  {Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv}
  {std_field: @field_theory F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (@eq F)}
  {Flist : list F}.

  Hypothesis Flist_unique : ulist Flist.
  Hypothesis Flist_F : forall x, In x Flist.
  Hypothesis Decidable_Feq : forall x y : F, {x = y} + {x <> y}.
  Notation q := (Z.of_nat (length Flist)).
  Hypothesis odd_order : (Z.odd q = true).
  Notation Fqstar := (@Fstar F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv std_field Flist Flist_unique Flist_F Decidable_Feq).
  Notation "x ^ n" := (@gpow F Fmul x Fqstar n).

  Add Field Fp : std_field.

  Lemma q_ge_2 : 2 <= q.
  Proof.
    unfold q. rewrite (ulist_rem_len F Decidable_Feq Flist Fone Flist_unique (Flist_F Fone)).
    destruct (remove Decidable_Feq Fone Flist) eqn:H; try (simpl; lia).
      - assert (contra : In Fzero (remove Decidable_Feq Fone Flist)) by (apply in_in_remove; auto; symmetry; apply (F_1_neq_0 std_field));
        rewrite H in contra; contradiction.
  Qed.


  Lemma even_order: Zeven (q - 1).
  Proof.
    apply Zodd_bool_iff in odd_order; apply Zodd_plus_Zodd; auto with zarith;
    assert (- (1) = Z.pred 0) as obv by auto with zarith; rewrite obv; apply Zodd_pred; auto with zarith.
  Qed.

  Lemma Zeven_ex_if n: Zeven n -> exists m, n = 2 * m.
  Proof. apply Zeven_ex_iff. Qed.



  Lemma gpow_gpow_nat: forall x n m, In x (s Fqstar) -> (x ^ ( Z.of_nat n)) ^ (Z.of_nat m) = (x ^ ((Z.of_nat n) * (Z.of_nat m))) .
  Proof.
    intros x n m Hx.
    induction m as [|m' IHm'].
      - simpl; assert (Z.of_nat n * 0 = 0) as obv by auto with zarith; rewrite obv; auto.
      - remember (Z.of_nat n) as n'; rewrite Nat2Z.inj_succ; remember (Z.of_nat m') as m''.
        assert (Z.succ m'' = m'' + 1) as nota by auto; rewrite nota.
        assert (n' * (m'' + 1) = n' * m'' + n' * 1) as nota2 by auto with zarith.
        assert (n' * 1 = n') as nota3 by auto with zarith; rewrite nota3 in nota2.
        rewrite nota2; repeat rewrite gpow_add; try (auto with zarith; apply gpow_in; auto).
        rewrite IHm'; rewrite gpow_1; [reflexivity | apply gpow_in; auto].
  Qed.

  Lemma zero_square: (Fzero) ^ 2 = Fzero.
  Proof. simpl; field. Qed.

  Lemma Fstar_order: (g_order Fqstar) = q - 1.
  Proof.
    unfold g_order. rewrite Fstar_list_len. apply Nat2Z.inj_pred. destruct Flist eqn:H.
      - pose proof Flist_F Fone; contradiction.
      - simpl; lia.
  Qed.

  Notation is_square x := (exists y, y^2 = x).

  Theorem square_criterion: forall x, In x (s Fqstar) -> x ^ ((q - 1) / 2) <> Fone -> ~(is_square x).
  Proof.
    intros x Hx H contra. pose proof q_ge_2 as H''. destruct contra as [x' H0].
    assert (Hx' : In x' (s Fqstar)) by
      (apply Fstar_list_elems; intros contra; rewrite contra in H0; pose proof zero_square as H';
      simpl in H'; simpl in H0; rewrite H' in H0; apply Fstar_list_elems in Hx; apply Hx; auto).
    assert (2 = Z.of_nat 2) as H2 by lia.
    pose proof (Zeven_ex_if (q - 1) even_order) as H1; destruct H1 as [x0 H1].
    assert (H1' := H1).
    apply (f_equal (fun y => y /2)) in H1; rewrite (Z.mul_comm 2), Z_div_mult_full in H1; try lia.
    assert (x0 = Z.of_nat( Z.to_nat (x0))) as Hx0.
      - rewrite Z2Nat.id; auto. rewrite <- H1. apply Z_div_pos; lia.
      - apply H; rewrite <- H0; rewrite H1, H2, Hx0, gpow_gpow_nat; auto.
        rewrite <- Hx0; rewrite <- H2; rewrite <- H1'; rewrite <- Fstar_order;
        apply fermat_gen; try apply decidable_Feq; auto.
  Qed.

  Instance Fstar_as_monoid : monoid (T := F) (eq := (@eq F)) (op := Fmul) (id := Fone).
  Proof. repeat split; (try apply _; try (intros; field)). Defined.

  Notation pos_pow := (@pow_pos F Fmul).

  Lemma rep_square_criterion: forall x (n : positive), In x (s Fqstar) -> x ^ (Zpos n) = pos_pow x n.
  Proof.
    intros x n; rewrite repeated_square_correct; pose proof positive_nat_Z n;
    rewrite <- H; destruct H; remember (Pos.to_nat n) as nnat eqn:Heqnnat; destruct Heqnnat;
    induction (nnat) as [| n' IHn']; auto...
      - intros H; assert (Z.of_nat (S n') = Z.of_nat n' + 1) as obv by apply Nat2Z.inj_succ.
        rewrite obv; rewrite gpow_add; try (auto; lia); rewrite IHn'; auto; simpl; field.
  Qed.

End Squaretest.