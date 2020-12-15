Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LinearSubstitute.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module WordByWordMontgomery.
  Section with_args.
    Context (lgr : Z)
            (m : Z).
    Local Notation weight := (uweight lgr).
    Let T (n : nat) := list Z.
    Let r := (2^lgr).
    Definition eval {n} : T n -> Z := Positional.eval weight n.
    Let zero {n} : T n := Positional.zeros n.
    Let divmod {n} : T (S n) -> T n * Z := Rows.divmod.
    Let scmul {n} (c : Z) (p : T n) : T (S n) (* uses double-output multiply *)
      := let '(v, c) := Rows.mul weight r n (S n) (Positional.extend_to_length 1 n [c]) p in
         v. About Rows.add.
    Let addT {n} (p q : T n) : T (S n) (* joins carry *)
      := let '(v, c) := Rows.add weight n p q in
         v ++ [c].
    Let SOS_red_add {n n'} (p : T n) ( q : T n') :  T (n)
        := let '(v,c) := (Rows.add weight n p (Positional.extend_to_length n' n q)) in
         v.
    Let drop_high_addT' {n} (p : T (S n)) (q : T n) : T (S n) (* drops carry *)
      := fst (Rows.add weight (S n) p (Positional.extend_to_length n (S n) q)).
    Let conditional_sub {n} (arg : T (S n)) (N : T n) : T n  (* computes [arg - N] if [N <= arg], and drops high bit *)
      := Positional.drop_high_to_length n (Rows.conditional_sub weight (S n) arg (Positional.extend_to_length n (S n) N)).
    Context (R_numlimbs : nat)
            (N : T R_numlimbs). (* encoding of m *)
    Let sub_then_maybe_add (a b : T R_numlimbs) : T R_numlimbs (* computes [a - b + if (a - b) <? 0 then N else 0] *)
      := fst (Rows.sub_then_maybe_add weight R_numlimbs (r-1) a b N).
      Let T_app {n} (p : T n) (e : Z) : T (S n)
      := p ++ [e].
    Local Opaque T.
    Section red_iteration.
    Context (pred_A_numlimbs : nat)
    (num_it : nat)
    (A : T (S pred_A_numlimbs))
    (k : Z).
  
    Local Definition A_s := dlet p := @divmod _ A in p. Local Definition A' := fst A_s. Local Definition s := snd A_s.
    Local Definition thism := fst (Z.mul_split r s k).
    Local Definition q := (@scmul _ thism N).
    Local Definition S1 := @SOS_red_add _ _ A q.
    Local Definition S2 := fst (@divmod _ S1).


    Local Definition red_steps
    :=  dlet A_s := @divmod _ A in
        dlet A' := fst A_s in
        dlet s := snd A_s in
        dlet thism := fst (Z.mul_split r s k) in
        dlet q := @scmul _ thism N in
        dlet S1 := @SOS_red_add _ _ A q in
        dlet S2 := fst (@divmod _ S1) in
        S2.

        Check red_steps.
        Check A.
        Check SOS_red_add.
    Lemma red_steps': red_steps = S2. Proof. reflexivity. Qed.
        
    End red_iteration.

    Section red_loop.
  Context (pred_A_numlimbs : nat)
  (N_numlimbs : nat)
  (num_it : nat)
  (A : T (S pred_A_numlimbs))
  (k : Z).

  Definition red_body {pred_A_numlimbs} : T (S pred_A_numlimbs) -> T pred_A_numlimbs
  := fun A => red_steps _ A k.

  Check red_body.
  Check red_steps.

  Definition red_loop (count : nat) : T (N_numlimbs + count + 1) -> T (N_numlimbs + 1)
  := nat_rect
  (fun count => T (N_numlimbs + count + 1)  -> _ )
  (fun A => A)
  (fun count' red_loop_count' A
  => red_loop_count' (red_body A))
  count.
  Definition pre_red : T (2 * N_numlimbs + 1)
  := (red_loop num_it (Positional.extend_to_length (2 * N_numlimbs) (2 * N_numlimbs + 1) A)).

    Definition red : T (R_numlimbs )
    := dlet res
      := conditional_sub (red_loop R_numlimbs (Positional.extend_to_length (2 * R_numlimbs) (2 * R_numlimbs + 1) A)) N in
      res.
End red_loop. 


    Create HintDb word_by_word_montgomery.
    Definition add (A B : T R_numlimbs) : T R_numlimbs
      := conditional_sub (@addT _ A B) N.
    Definition sub (A B : T R_numlimbs) : T R_numlimbs
      := sub_then_maybe_add A B.
    Definition opp (A : T R_numlimbs) : T R_numlimbs
      := sub (@zero _) A.
    Definition nonzero (A : list Z) : Z
      := fold_right Z.lor 0 A.

    Context (lgr_big : 0 < lgr)
            (R_numlimbs_nz : R_numlimbs <> 0%nat).
    Let R := (r^Z.of_nat R_numlimbs).
    Transparent T.
    Definition small {n} (v : T n) : Prop
      := v = Partition.partition weight n (eval v).
    Definition sc_small sc : Prop
      := 0 <= sc < r.  
    Context (small_N : small N)
            (N_lt_R : eval N < R)
            (N_nz : 0 < eval N)
            (B : T R_numlimbs)
            (B_bounds : 0 <= eval B < R)
            (small_B : small B)
            ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
            (k : Z) (k_correct : k * eval N mod r = (-1) mod r)
            (numbits_big: Z.of_nat R_numlimbs < r).

    Local Lemma r_big : r > 1.
    Proof using lgr_big. clear -lgr_big; subst r. auto with zarith. Qed.
    Local Notation wprops := (@uwprops lgr lgr_big).

    Local Hint Immediate (wprops) : core.
    Local Hint Immediate (weight_0 wprops) : core.
    Local Hint Immediate (weight_positive wprops) : core.
    Local Hint Immediate (weight_multiples wprops) : core.
    Local Hint Immediate (weight_divides wprops) : core.
    Local Hint Immediate r_big : core.

    Lemma length_small {n v} : @small n v -> length v = n.
    Proof using Type. clear; cbv [small]; intro H; rewrite H; autorewrite with distr_length; reflexivity. Qed.
    Lemma small_bound {n v} : @small n v -> 0 <= eval v < weight n.
    Proof using lgr_big. clear - lgr_big; cbv [small eval]; intro H; rewrite H; autorewrite with push_eval; auto with zarith. Qed.

    Lemma R_plusR_le : R + R <= weight (S R_numlimbs).
    Proof using lgr_big.
      clear - lgr_big.
      etransitivity; [ | apply uweight_double_le; lia ].
      rewrite uweight_eq_alt by lia.
      subst r R; lia.
    Qed.

    Lemma mask_r_sub1 n x :
      map (Z.land (r - 1)) (Partition.partition weight n x) = Partition.partition weight n x.
    Proof using lgr_big.
      clear - lgr_big. cbv [Partition.partition].
      rewrite map_map. apply map_ext; intros.
      rewrite uweight_S by lia.
      rewrite <-Z.mod_pull_div by auto with zarith.
      replace (r - 1) with (Z.ones lgr) by (rewrite Z.ones_equiv; subst r; reflexivity).
      rewrite <-Z.land_comm, Z.land_ones by lia.
      auto with zarith.
    Qed.

    Let partition_Proper := (@Partition.partition_Proper _ wprops).
    Local Existing Instance partition_Proper.
    Lemma eval_nonzero n A : @small n A -> nonzero A = 0 <-> @eval n A = 0.
    Proof using lgr_big.
      clear -lgr_big partition_Proper.
      cbv [nonzero eval small]; intro Heq.
      do 2 rewrite Heq.
      rewrite !eval_partition, Z.mod_mod by auto with zarith.
      generalize (Positional.eval weight n A); clear Heq A.
      induction n as [|n IHn].
      { cbn; rewrite weight_0 by auto; intros; autorewrite with zsimplify_const; lia. }
      { intro; rewrite partition_step.
        rewrite fold_right_snoc, Z.lor_comm, <- fold_right_push, Z.lor_eq_0_iff by auto using Z.lor_assoc.
        assert (Heq : Z.equiv_modulo (weight n) (z mod weight (S n)) (z mod (weight n))).
        { cbv [Z.equiv_modulo].
          generalize (weight_multiples ltac:(auto) n).
          generalize (weight_positive ltac:(auto) n).
          generalize (weight_positive ltac:(auto) (S n)).
          generalize (weight (S n)) (weight n); clear; intros wsn wn.
          clear; intros.
          Z.div_mod_to_quot_rem; subst.
          autorewrite with zsimplify_const in *.
          Z.linear_substitute_all.
          apply Zminus_eq; ring_simplify.
          rewrite <- !Z.add_opp_r, !Z.mul_opp_comm, <- !Z.mul_opp_r, <- !Z.mul_assoc.
          rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
          nia. }
        rewrite Heq at 1; rewrite IHn.
        rewrite Z.mod_mod by auto with zarith.
        generalize (weight_multiples ltac:(auto) n).
        generalize (weight_positive ltac:(auto) n).
        generalize (weight_positive ltac:(auto) (S n)).
        generalize (weight (S n)) (weight n); clear; intros wsn wn; intros.
        Z.div_mod_to_quot_rem.
        repeat (intro || apply conj); destruct_head'_or; try lia; destruct_head'_and; subst; autorewrite with zsimplify_const in *; try nia;
          Z.linear_substitute_all.
        all: apply Zminus_eq; ring_simplify.
        all: rewrite <- ?Z.add_opp_r, ?Z.mul_opp_comm, <- ?Z.mul_opp_r, <- ?Z.mul_assoc.
        all: rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
        all: nia. }
    Qed.

    Definition app_hyp v1 : list Z -> Prop
    := fun v2 => 
        (
          @eval (length v1 + length v2) (v1 ++ v2) = @eval (length v1) v1 + r ^ Z.of_nat (length v1) * @eval (length v2) v2
        ).

        Lemma eval_sc: forall sc, @eval 1 [sc] = sc.
    Proof.
      intros. unfold eval, Positional.eval, Associational.eval, Positional.to_associational.
      simpl. rewrite weight_0; [auto with zarith | apply wprops].
    Qed. 

    Lemma eval_app: forall (n1 n2 : nat) v1 v2, length v1 = n1 -> length v2 = n2 -> @eval (n1 + n2) (v1 ++ v2) = @eval n1 v1 + (r ^ (Z.of_nat (length v1)) * (@eval n2 v2)).
    Proof.
      intros. generalize dependent n1. generalize dependent n2.
      pose proof (@rev_ind Z (app_hyp v1)). unfold app_hyp in H. intros. unfold eval.
      rewrite <- H1. rewrite <- H0. apply H.
        - unfold eval. rewrite Positional.eval_nil. rewrite Z.mul_0_r. simpl.
          repeat rewrite Z.add_0_r. Local Close Scope Z_scope. assert (length v1 + 0 = length v1) by auto.
          rewrite H2. rewrite app_nil_r. auto.
        - intros. unfold eval. rewrite app_length. simpl. Search (_ + 1). rewrite Nat.add_1_r.
          assert (v1 ++ l ++ [x] = (v1 ++ l) ++ [x]) by apply app_assoc. rewrite H3.
          Search (_ + S _). rewrite NPeano.Nat.add_succ_r.
          rewrite Positional.eval_snoc_S. rewrite Positional.eval_snoc_S.
          simpl. unfold eval in H2. rewrite H2. simpl.
          rewrite Z.mul_add_distr_l. rewrite Z.mul_assoc. About Weight. rewrite uweight_sum_indices.
          rewrite uweight_eq_alt. unfold r. auto with zarith.
          all: try rewrite app_length; auto with zarith. Local Open Scope Z_scope.
    Qed.

    Local Ltac push_step :=
      first [ progress eta_expand
            | rewrite Rows.mul_partitions
            | rewrite Rows.mul_div
            | rewrite Rows.add_partitions
            | rewrite Rows.add_div
            | progress autorewrite with push_eval distr_length
            | match goal with
              | [ H : ?v = _ |- context[length ?v] ] => erewrite length_small by eassumption
              | [ H : small ?v |- context[length ?v] ] => erewrite length_small by eassumption
              end
            | rewrite Positional.eval_cons by distr_length
            | progress rewrite ?weight_0, ?uweight_1 by auto;
              autorewrite with zsimplify_fast
            | rewrite (weight_0 wprops)
            | rewrite <- Z.div_mod'' by auto with lia
            | solve [ trivial ] ].
    Local Ltac push := repeat push_step.

    Local Ltac t_step :=
      match goal with
      | [ H := _ |- _ ] => progress cbv [H] in *
      | _ => progress push_step
      | _ => progress autorewrite with zsimplify_const
      | _ => solve [ auto with lia ]
      end.

    Local Hint Unfold eval zero small divmod scmul drop_high_addT' addT R : loc.
    Local Lemma eval_zero : forall n, eval (@zero n) = 0.
    Proof using Type.
      clear; autounfold with loc; intros; autorewrite with push_eval; auto.
    Qed.
    Local Lemma small_zero : forall n, small (@zero n).
    Proof using Type.
      etransitivity; [ eapply Positional.zeros_ext_map | rewrite eval_zero ]; cbv [Partition.partition]; cbn; try reflexivity; autorewrite with distr_length; reflexivity.
    Qed.
    Local Hint Immediate small_zero : core.


    Ltac push_recursive_partition :=
      repeat match goal with
             | _ => progress cbn [recursive_partition]
             | H : small _ |- _ => rewrite H; clear H
             | _ => rewrite recursive_partition_equiv by auto using wprops
             | _ => rewrite uweight_eval_shift by distr_length
             | _ => progress push
             end.

    Lemma length_SOS_red_add: forall n1 n2 (A : T n1) (B : T n2), length A = n1 -> length B = n2 -> (n2 <= n1)%nat -> length (SOS_red_add A B) = length A.
    Proof.
      intros. unfold SOS_red_add. simpl. Search (length (fst (Rows.add))). About Rows.add.
      rewrite Saturated.Rows.length_sum_rows with (n := length A).
        - auto.
        - apply wprops.
        - auto.
        - rewrite Positional.length_extend_to_length.
          + auto.
          + auto.
          + auto.
    Qed.

    Lemma eval_div : forall n v, small v -> eval (fst (@divmod n v)) = eval v / r.
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - r_big lgr_big; intros; autounfold with loc.
      push_recursive_partition; cbn [Rows.divmod fst tl].
      autorewrite with zsimplify; reflexivity.
    Qed.
    Lemma eval_mod : forall n v, small v -> snd (@divmod n v) = eval v mod r.
    Proof using lgr_big.
      clear - lgr_big; intros; autounfold with loc.
      push_recursive_partition; cbn [Rows.divmod snd hd].
      autorewrite with zsimplify; reflexivity.
    Qed.

    Lemma small_div : forall n v, small v -> small (fst (@divmod n v)).
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - r_big lgr_big. intros; autounfold with loc.
      push_recursive_partition. cbn [Rows.divmod fst tl].
      rewrite <-recursive_partition_equiv by auto.
      rewrite <-uweight_recursive_partition_equiv with (i:=1%nat) by lia.
      push.
      apply Partition.partition_Proper; [ solve [auto] | ].
      cbv [Z.equiv_modulo]. autorewrite with zsimplify.
      reflexivity.
    Qed.

    Definition canon_rep {n} x (v : T n) : Prop :=
      (v = Partition.partition weight n x) /\ (0 <= x < weight n).
    Lemma eval_canon_rep n x v : @canon_rep n x v -> eval v = x.
    Proof using lgr_big.
      clear - lgr_big.
      cbv [canon_rep eval]; intros [Hv Hx].
      rewrite Hv. autorewrite with push_eval.
      auto using Z.mod_small.
    Qed.
    Lemma small_canon_rep n x v : @canon_rep n x v -> small v.
    Proof using lgr_big.
      clear - lgr_big.
      cbv [canon_rep eval small]; intros [Hv Hx].
      rewrite Hv. autorewrite with push_eval.
      apply partition_eq_mod; auto; [ ].
      Z.rewrite_mod_small; reflexivity.
    Qed.


    Lemma small_nil: @small 0 [].
    Proof. reflexivity. Qed.
    
    Definition small_crit n v := (Forall sc_small v) /\ (length v = n).

    Lemma length_S_app: forall (l: list Z) n, length l = S n -> exists l' a, l = @T_app (n) l' a.
    Proof. intros l. apply (rev_ind (fun (y : list Z) => (forall n, length y = S (n) -> exists l' a, y = l' ++ [a]))).
      - intros. discriminate.
      - intros. exists l0, x. auto.
    Qed.

    Lemma weight_value: forall n, weight n = r ^ (Z.of_nat n).
    Proof.
      intros; rewrite uweight_eq_alt'; apply Z.pow_mul_r; lia.
    Qed.

    Lemma r_pow_S : forall n, r ^ (Z.of_nat (S n)) = r ^ (Z.of_nat n) * r.
    Proof.
      intros; rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r; auto with zarith.
    Qed.

    Lemma sc_small_length_small: forall n (v: T n), length v = n -> Forall sc_small v -> small v.
    Proof. intros. generalize dependent v. induction n.
        - intros. rewrite length_zero_iff_nil in H. rewrite H. apply small_nil.
        - intros. assert (H': length v = S n) by auto. apply length_S_app in H. destruct H, H.
          assert (small x).
            + apply IHn. apply (f_equal (fun (y : list Z) => length y)) in H. unfold T_app in H.
              rewrite app_length in H. rewrite H' in H. simpl in H. rewrite Nat.add_1_r in H. inversion H.
              auto.
              unfold T_app in H. rewrite H in H0. rewrite Forall_app in H0. destruct H0. auto.
            + unfold T_app in H. rewrite H. unfold small. rewrite Partition.partition_step.
              rewrite H in H'. rewrite app_length in H'. simpl in H'.
              rewrite Nat.add_1_r in H'. inversion H'.
              assert (Partition.partition weight n (@eval (S n) (x ++ [x0])) = Partition.partition weight n (@eval n (x))).
                { apply Partition.partition_eq_mod; auto. rewrite <- Nat.add_1_r.
                  rewrite eval_app; auto. rewrite H3.
                   rewrite weight_value. rewrite Z.mod_add'_full. auto. }
              assert (@eval (S n) (x ++ [x0]) mod weight (S n) / weight n = x0).
              {
                rewrite <- Nat.add_1_r. rewrite eval_app; auto.
                Search ( (_ + _) / _ ). rewrite uweight_pull_mod; auto with zarith.
                assert (n + 1 - n = 1)%nat by auto with zarith. rewrite H4.
                rewrite (weight_value n). rewrite H3. rewrite Z.div_add'.
                Search (_ / _ = 0). rewrite Zdiv_small.
                  - rewrite eval_sc. simpl. apply Z.mod_small.
                    assert (sc_small x0).
                      + apply (Forall_forall sc_small v); auto. rewrite H. Search (In (_ ++ _)).
                        apply in_or_app. right. simpl. auto.
                      + unfold sc_small in H5. rewrite weight_value. auto with zarith.
                  - apply small_bound in H1. rewrite weight_value in H1. auto.
                  - unfold r; auto with zarith.
              }
              unfold small in H1. rewrite H3, H2, H4. rewrite <- H1. auto.
    Qed.

    Lemma small_rem: forall n (v : T n) x, @small (S n) (v ++ [x]) -> small v.
    Proof.
      intros. pose proof (length_small H). rewrite app_length in H0. rewrite Nat.add_1_r in H0. inversion H0.
      unfold small in H. rewrite Partition.partition_step in H. rewrite <- Nat.add_1_r in H. rewrite eval_app in H; auto.
      Search ((_ ++ [_]) = (_ ++ [_])). apply app_inj_tail in H. destruct H.
      unfold small.
      assert ( Partition.partition weight n
      (eval v + r ^ Z.of_nat (length v) * @eval 1 [x]) = Partition.partition weight (length v) (eval v)).
        - rewrite H2. apply Partition.partition_eq_mod; auto.
          rewrite weight_value. rewrite Z.mod_add'_full. auto.
        - rewrite H2. rewrite H2 in H3. rewrite <- H3. auto. rewrite H2 in H. auto.
    Qed.

    Lemma small_sc_small: forall n (v : T n), small v -> Forall sc_small v.
    Proof. intros.
      apply (rev_ind (fun v => (@small (length v) v -> Forall sc_small v))); auto.
      intros. rewrite Forall_app; split.
        - apply H0. Set Printing All. apply (small_rem) with (x := x). auto. simpl in H1.
          unfold small in H1. unfold small. rewrite app_length in H1. simpl in H1. rewrite Nat.add_1_r in H1. auto.
        - apply Forall_cons; auto. unfold small in H1.
          rewrite app_length in H1. simpl in H1. rewrite Nat.add_1_r in H1. rewrite Partition.partition_step in H1.
          apply app_inj_tail in H1. destruct H1. rewrite uweight_pull_mod in H2; auto; try lia.
          assert (forall n, (S n - n = 1)% nat). auto with zarith. rewrite H3 in H2. rewrite weight_value in H2.
          Search ((_ mod _) < _). unfold sc_small. rewrite H2. rewrite weight_value.
          assert (r ^ Z.of_nat 1 = r). auto with zarith. rewrite H4. apply Z.mod_pos_bound. unfold r. auto with zarith.
        - pose proof (length_small H). rewrite H0. auto.
    Qed.

    Lemma small_if_Forall_sc_small: forall n (v : T n),
    small v <-> (length v = n) /\ (Forall sc_small v).
    Proof.
      repeat split; intros; [apply length_small; auto| apply small_sc_small; auto| apply sc_small_length_small; destruct H; auto].
    Qed.
    
    Lemma small_s_mod: forall n (A : T (S n)), small A -> with_args.s n A = eval A mod r.
    Proof.
      intros. unfold s. simpl. apply small_if_Forall_sc_small in H. destruct H.
      destruct A.
        - simpl. unfold eval. rewrite Positional.eval_nil. auto.
        - simpl. Search (Forall _ (_ :: _)). apply Forall_inv in H0. unfold sc_small in H0.
          assert (z :: A = ([z] ++ A)). auto.
          rewrite H1. pose proof (eval_app 1 n [z] A).
          Set Printing All. assert ((Init.Nat.add (S O) n) = (S n)). auto.
          Set Printing All.
          rewrite H3 in H2.
          rewrite H2.
          simpl. Search (Z.pow_pos _ 1). rewrite Zpow_facts.Zpower_pos_1_r.
          rewrite Z.mod_add'.
          rewrite Z.mod_small. rewrite eval_sc; auto. rewrite eval_sc; auto.
          auto with zarith.
          auto.
          auto.
    Qed.

    Local Lemma scmul_correct: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> canon_rep (a * eval v) (@scmul n a v).
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - lgr_big r_big.
      autounfold with loc; intro n; destruct (zerop n); intros *; intro Hsmall; intros.
      { intros; subst; cbn; rewrite Z.add_with_get_carry_full_mod.
        split; cbn; autorewrite with zsimplify_fast; auto with zarith. }
      { rewrite (surjective_pairing (Rows.mul _ _ _ _ _ _)).
        rewrite Rows.mul_partitions by (try rewrite Hsmall; auto using length_partition, Positional.length_extend_to_length with lia).
        autorewrite with push_eval.
        rewrite Positional.eval_cons by reflexivity.
        rewrite weight_0 by auto.
        autorewrite with push_eval zsimplify_fast.
        split; [reflexivity | ].
        rewrite uweight_S, uweight_eq_alt by lia.
        subst r; nia. }
    Qed.

    Lemma length_sc_mul: forall n v sc, n <> O -> length v = n -> length (@scmul n sc v) = S (length v).
    Proof.
      intros. unfold scmul. destruct (Rows.mul weight r n (S n)) eqn:eq1.
      apply (f_equal (fun y => fst y)) in eq1.
      apply (f_equal (fun (y : list Z) => length y)) in eq1. rewrite Rows.length_mul in eq1. simpl in eq1. rewrite H0.
      all: auto. simpl. rewrite Positional.length_zeros. auto with zarith.
    Qed.

    Local Lemma addT_correct : forall n a b, small a -> small b -> canon_rep (eval a + eval b) (@addT n a b).
    Proof using lgr_big.
      intros n a b Ha Hb.
      generalize (length_small Ha); generalize (length_small Hb).
      generalize (small_bound Ha); generalize (small_bound Hb).
      clear -lgr_big Ha Hb.
      autounfold with loc; destruct (zerop n); subst.
      { destruct a, b; cbn; try lia; split; auto with zarith. }
      { pose proof (uweight_double_le lgr ltac:(lia) n).
        eta_expand; split; [ | lia ].
        rewrite Rows.add_partitions, Rows.add_div by auto.
        rewrite partition_step.
        Z.rewrite_mod_small; reflexivity. }
    Qed.

    Local Lemma drop_high_addT'_correct : forall n a b, small a -> small b -> canon_rep ((eval a + eval b) mod (r^Z.of_nat (S n))) (@drop_high_addT' n a b).
    Proof using lgr_big.
      intros n a b Ha Hb; generalize (length_small Ha); generalize (length_small Hb).
      clear -lgr_big Ha Hb.
      autounfold with loc in *; subst; intros.
      rewrite Rows.add_partitions by auto using Positional.length_extend_to_length.
      autorewrite with push_eval.
      split; try apply partition_eq_mod; auto; rewrite uweight_eq_alt by lia; subst r; Z.rewrite_mod_small; auto with zarith.
    Qed.

    Local Lemma conditional_sub_correct : forall v, small v -> 0 <= eval v < eval N + R -> canon_rep (eval v + (if eval N <=? eval v then -eval N else 0)) (conditional_sub v N).
    Proof using small_N lgr_big N_nz N_lt_R.
      pose proof R_plusR_le as R_plusR_le.
      clear - small_N lgr_big N_nz N_lt_R R_plusR_le.
      intros; autounfold with loc; cbv [conditional_sub].
      repeat match goal with H : small _ |- _ =>
                             rewrite H; clear H end.
      autorewrite with push_eval.
      assert (weight R_numlimbs < weight (S R_numlimbs)) by (rewrite !uweight_eq_alt by lia; autorewrite with push_Zof_nat; auto with zarith).
      assert (eval N mod weight R_numlimbs < weight (S R_numlimbs)) by (pose proof (Z.mod_pos_bound (eval N) (weight R_numlimbs) ltac:(auto)); lia).
      rewrite Rows.conditional_sub_partitions by (repeat (autorewrite with distr_length push_eval; auto using partition_eq_mod with zarith)).
      rewrite drop_high_to_length_partition by lia.
      autorewrite with push_eval.
      assert (weight R_numlimbs = R) by (rewrite uweight_eq_alt by lia; subst R; reflexivity).
      Z.rewrite_mod_small.
      break_match; autorewrite with zsimplify_fast; Z.ltb_to_lt.
      { split; [ reflexivity | ].
        rewrite Z.add_opp_r. fold (eval N).
        auto using Z.mod_small with lia. }
      { split; auto using Z.mod_small with lia. }
    Qed.

    Local Lemma sub_then_maybe_add_correct : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> canon_rep (eval a - eval b + (if eval a - eval b <? 0 then eval N else 0)) (sub_then_maybe_add a b).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R.
      pose proof mask_r_sub1 as mask_r_sub1.
      clear - small_N lgr_big R_numlimbs_nz N_nz N_lt_R mask_r_sub1.
      intros; autounfold with loc; cbv [sub_then_maybe_add].
      repeat match goal with H : small _ |- _ =>
                             rewrite H; clear H end.
      rewrite Rows.sub_then_maybe_add_partitions by (autorewrite with push_eval distr_length; auto with zarith).
      autorewrite with push_eval.
      assert (weight R_numlimbs = R) by (rewrite uweight_eq_alt by lia; subst r R; reflexivity).
      Z.rewrite_mod_small.
      split; [ reflexivity | ].
      break_match; Z.ltb_to_lt; lia.
    Qed.
    Check Positional.zeros.

    Lemma nat_sub: forall x y, (S x <= y)%nat -> S (y - S x) = (y - x)%nat.
    Proof.
       intros. rewrite <- Nat.sub_succ_l. rewrite NPeano.Nat.sub_succ; auto. auto. Qed.

     Lemma nat_sub_0: forall y : nat, (y - 0)%nat = y.
     Proof. auto with zarith. Qed.

     Lemma nat_0_add_r: forall y, (0 + y)%nat = y.
     Proof. auto. Qed.

    Lemma extend_app: forall n1 n2 v, Positional.extend_to_length (n1) (n1 + n2) v = (v ++ (Positional.zeros n2)).
    Proof.
      intros. unfold Positional.extend_to_length. assert ((n1 + n2 - n1)%nat = n2) by auto with zarith.
      rewrite H. auto.
    Qed.

    Lemma extend_length: forall n1 n2 v, (length v = n2)%nat -> (n2 <= n1)%nat -> length (Positional.extend_to_length n2 n1 v) = n1.
    Proof.
      intros. assert (n1 = n2 + (n1 - n2))%nat by auto with zarith. rewrite H1. rewrite extend_app.
      rewrite app_length. rewrite Positional.length_zeros. auto.
    Qed.

    Lemma zeros_S: forall n, Positional.zeros (S n) = (Positional.zeros n ++ [0%Z]).
    Proof. intros. simpl.
      induction n.
        - simpl. unfold Positional.zeros. simpl. auto.
        - unfold Positional.zeros in IHn. simpl in IHn.
          unfold Positional.zeros. simpl. rewrite IHn. auto.
    Qed.

    Lemma weight_geq: forall n1 n2, ((weight n1) <= (weight (n1 + n2)))%Z.
    Proof. intros. induction n2.
      - simpl. rewrite Nat.add_0_r. lia.
      - Search (_ + S _). rewrite NPeano.Nat.add_succ_r. simpl. pose proof wprops.
        destruct H. assert ((weight (n1 + n2) <= (weight (S (n1 + n2))))%Z).
          + unfold weight. unfold ModOps.weight. Search (_ / 1)%Z. repeat rewrite Z.div_1_r.
            Search (- (- _))%Z. repeat rewrite Z.opp_involutive. auto with zarith.
          + lia.
    Qed.

    Local Close Scope Z_scope.
    Lemma weight_geq': forall n1 n2, n2 <= n1 -> ((weight n2) <= (weight n1))%Z.
    Proof.
      intros. assert ((n1 = (n2 + (n1 - n2)))). auto with zarith. rewrite H0.
      apply weight_geq.
    Qed.

    Lemma Partition_long: forall n1 n2 (v : T n1), small v -> Partition.partition weight (n1 + n2) (eval v) = v ++ (Positional.zeros n2).
    Proof.
      induction n2.
      - intros. rewrite Nat.add_0_r. simpl. unfold Positional.zeros. simpl.
        rewrite <- H. rewrite app_nil_r. auto.
      - intros. Search (_ + S _). rewrite NPeano.Nat.add_succ_r.
        rewrite Partition.partition_step. rewrite Z.mod_small.
        Search Z.div. rewrite  Z.div_small. rewrite IHn2. rewrite zeros_S.
        rewrite app_assoc. auto. Search small.
        auto. 
          + pose proof (small_bound H). pose proof (weight_geq n1 n2). lia.
          + pose proof (small_bound H). pose proof (weight_geq n1 (S n2)). rewrite <- NPeano.Nat.add_succ_r. lia.
    Qed.

    Lemma undo_div: forall n1 n2: nat, forall A : list Z, length A <> O -> A = snd (@divmod n1 A) :: (fst (@divmod n2 A)).
    Proof. intros. destruct A; [contradiction| auto]. Qed.


    Lemma small_exten: forall n1 (n2: nat) (v : T n2), (n2 <= n1)%nat -> small v -> @small n1 (Positional.extend_to_length n2 n1 v).
    Proof. intros. Search small. apply small_canon_rep with (x := (eval v)). split.
      - assert ((n1 = n2 + (n1 - n2))%nat) by auto with zarith. rewrite H1. rewrite Partition_long.
        simpl. rewrite <- H1. reflexivity. auto.
      - pose proof (small_bound H0). pose proof (weight_geq' n1 n2). lia.
    Qed.

  Check SOS_red_add. Local Open Scope Z_scope.

    Local Lemma eval_scmul: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> eval (@scmul n a v) = a * eval v.
    Proof using lgr_big. eauto using scmul_correct, eval_canon_rep. Qed.
    Local Lemma small_scmul : forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> small (@scmul n a v).
    Proof using lgr_big. eauto using scmul_correct, small_canon_rep. Qed.
    Local Lemma eval_addT : forall n a b, small a -> small b -> eval (@addT n a b) = eval a + eval b.
    Proof using lgr_big. eauto using addT_correct, eval_canon_rep. Qed.
    Local Lemma small_addT : forall n a b, small a -> small b -> small (@addT n a b).
    Proof using lgr_big. eauto using addT_correct, small_canon_rep. Qed.
    Local Lemma eval_drop_high_addT' : forall n a b, small a -> small b -> eval (@drop_high_addT' n a b) = (eval a + eval b) mod (r^Z.of_nat (S n)).
    Proof using lgr_big. eauto using drop_high_addT'_correct, eval_canon_rep. Qed.
    Local Lemma small_drop_high_addT' : forall n a b, small a -> small b -> small (@drop_high_addT' n a b).
    Proof using lgr_big. eauto using drop_high_addT'_correct, small_canon_rep. Qed.
    Local Lemma eval_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> eval (conditional_sub v N) = eval v + (if eval N <=? eval v then -eval N else 0).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, eval_canon_rep. Qed.
    Local Lemma small_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> small (conditional_sub v N).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, small_canon_rep. Qed.
    Local Lemma eval_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> eval (sub_then_maybe_add a b) = eval a - eval b + (if eval a - eval b <? 0 then eval N else 0).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, eval_canon_rep. Qed.
    Local Lemma small_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> small (sub_then_maybe_add a b).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, small_canon_rep. Qed.
          

    Lemma eval_extend: forall n1 n2 (v : T n2), (n2 <= n1)%nat -> length v = n2 -> eval v =  @eval n1 (Positional.extend_to_length n2 n1 v).
    Proof. intros. assert (n1 = n2 + (n1 - n2))%nat by auto with zarith. rewrite H1. rewrite extend_app.
      rewrite eval_app; try rewrite Positional.length_zeros; auto. rewrite eval_zero. auto with zarith.
    Qed.

    Lemma small_SOS_red_add: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 -> small (SOS_red_add v1 v2).
    Proof. intros.
      destruct n1 eqn:eq1.
        - assert (n2 = 0)%nat by auto with zarith. apply length_small in H0. apply length_small in H1.
          rewrite H2 in H1. Search (length _ = O). apply length_zero_iff_nil in H0.
          apply length_zero_iff_nil in H1. rewrite H0, H1.
          unfold SOS_red_add. simpl. apply small_nil.
         - intros. unfold SOS_red_add. assert (@small n1 (Positional.extend_to_length n2 n1 v2)) by (apply small_exten; auto; lia).
          rewrite eq1 in H2.
          pose proof (small_addT (S n) v1 (Positional.extend_to_length n2 (S n) v2) H0 H2). unfold addT in H3.
          remember ( Rows.add weight (S n) v1 (Positional.extend_to_length n2 (S n) v2)) as v'.
          destruct v'. apply small_rem with (x := z). auto.
    Qed.
    

    Lemma eval_SOS_red_add_mod: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 -> eval (SOS_red_add v1 v2) = (eval v1 + eval v2) mod r ^ Z.of_nat n1.
    Proof.
      intros. unfold SOS_red_add. simpl. unfold eval. rewrite Rows.sum_rows_mod; auto.
        - rewrite weight_value. rewrite <- eval_extend with (n1 := n1); try apply length_small; auto.
        - apply length_small; auto.
        - rewrite extend_length; try apply length_small; auto.
    Qed.

    Lemma eval_SOS_add_full: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
      eval (SOS_red_add v1 v2) + (weight n1 * ((eval v1 + eval v2) / weight n1)) = (eval v1 + eval v2).
    Proof.
      intros. unfold SOS_red_add. simpl. unfold eval. rewrite Rows.sum_rows_mod; try apply extend_length; try apply length_small; auto.
      rewrite <- eval_extend with (n1 := n1); try apply length_small; auto.  rewrite <- Z.div_mod''; auto.
    Qed.

    Lemma eval_SOS_add_full': forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
    eval (SOS_red_add v1 v2) = (eval v1 + eval v2) - (weight n1 * ((eval v1 + eval v2) / weight n1)).
  Proof.
    intros. pose proof (eval_SOS_add_full n1 n2 v1 v2 H H0 H1). apply (f_equal (fun y => y - (weight n1 * ((eval v1 + eval v2) / weight n1)))) in H2.
    assert (forall (x : Z) y, x + y - y = x). auto with zarith. rewrite H3 in H2. auto.
  Qed.

  Lemma eval_SOS_add_small: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
    (eval v1 + eval v2) < (weight n1)  -> eval (SOS_red_add v1 v2) = (eval v1 + eval v2).
  Proof.
    intros. rewrite eval_SOS_add_full'; auto. rewrite Zdiv_small; auto with zarith.
    apply small_bound in H0. apply small_bound in H1. lia.
  Qed.

  Lemma eval_SOS_bound: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
    eval (SOS_red_add v1 v2) <= eval v1 + eval v2.
  Proof.
    intros. rewrite <- eval_SOS_add_full; auto with zarith. Search (?n1 <= ?n1 + _).
    pose proof (@small_bound _ v1 H0). pose proof (@small_bound _ v2 H1).
    assert (0 <= eval v1 + eval v2) by lia. assert (0 <= (eval v1 + eval v2) / weight n1 ). apply Z.div_nonneg.
     lia. lia. assert (0 <= weight n1 * ((eval v1 + eval v2) / weight n1)). Search (0 <= _ * _).
     apply Z.mul_nonneg_nonneg; lia. lia.
  Qed.

  Lemma smallthism': forall n (A : T (S n)), sc_small (thism n A k).
  Proof. intros. unfold thism; rewrite Z.mul_split_mod; unfold sc_small; auto with zarith. Qed. 


  Lemma add_q_low_word: forall n (A : T (S n)), small A -> (eval A + eval (q n A k)) mod r = 0.
  Proof.
    intros. unfold q. rewrite eval_scmul; auto; try lia. unfold thism. Search (Z.mul_split).
    rewrite Z.mul_split_mod. rewrite small_s_mod. rewrite Z.add_mod.
    rewrite Z.mul_mod. repeat rewrite Z.mod_mod. rewrite <- Z.mul_mod.
    rewrite <- Z.mul_assoc. rewrite Z.mul_mod. rewrite k_correct.
    rewrite <- Z.mul_mod. Search (_ * (-1)). rewrite <- Z.opp_eq_mul_m1.
    Search (_ + (- _)).
    rewrite <- Z.add_mod. rewrite Z.add_opp_r.
    rewrite Zminus_mod. rewrite Z.mod_mod. rewrite <- Zminus_mod.
    Search (_ - _ = 0). rewrite Z.sub_diag. all: try unfold r; auto with zarith.
    pose proof (smallthism' n A). unfold sc_small in H0. auto.
  Qed.



  Lemma r_nz: r <> 0.
  Proof.
    unfold r. auto with zarith.
  Qed.

    Lemma small_carry: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 ->
    ((eval v1 + eval v2) / weight n1) <= 1.
    Proof.
      intros. apply Z.div_floor; auto. simpl.  apply small_bound in H0. apply small_bound in H1.
      pose proof (weight_geq' n1 n2 H). lia.
    Qed.

    Check S1.
    Check s.

    Lemma S1_mod_r: forall n (A : T (S n)), (R_numlimbs <= n)%nat -> small A -> eval (S1 n A k) mod r = 0.
    Proof. intros n A H'' H'.
      unfold S1. rewrite eval_SOS_add_full'; auto; try lia. Set Printing All. Search ((_ - _) mod _).
      rewrite Zminus_mod. rewrite weight_value. Search (r ^ _). rewrite r_pow_S.
      rewrite Z.mul_comm.
      rewrite Z.mul_assoc. rewrite Z.mod_mul. simpl. Search (_ - 0). rewrite Z.sub_0_r.
      rewrite Z.mod_mod. unfold q. unfold thism. rewrite eval_scmul. Search (fst (Z.mul_split _ _ _)).
      rewrite Z.mul_split_mod. rewrite Z.add_mod. rewrite Z.mul_mod. rewrite Z.mod_mod.
      rewrite (Z.mul_mod _ k _). rewrite <- Z.mul_mod. rewrite <- Z.mul_assoc. rewrite Z.mul_mod.
      rewrite (Z.mul_mod _ (eval N) _). repeat rewrite Z.mod_mod.
      rewrite <- (Z.mul_mod k _ _). rewrite k_correct.
      rewrite <- Z.mul_mod. rewrite <- Z.add_mod. Search (_ * (-1)).
      rewrite <- Z.opp_eq_mul_m1. rewrite Z.add_opp_r. Set Printing All.
      
      rewrite small_s_mod. Set Printing All.
      rewrite Zminus_mod. rewrite Z.mod_mod. Search (?n1 - ?n1).
      rewrite <- Zminus_mod. rewrite Z.sub_diag. all: (try apply r_nz; auto with zarith).
      Search (fst (Z.mul_split _ _ _)). rewrite Z.mul_split_mod.
      apply Z_mod_lt. unfold r; auto with zarith.
      unfold q. apply small_scmul; auto. apply smallthism'.
      lia.
    Qed.

    (* Lemma eval_SOS_red_add_mod: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 -> eval (SOS_red_add v1 v2) = (eval v1 + eval v2) mod r ^ Z.of_nat n1.
    Proof.
      intros. unfold SOS_red_add. simpl. unfold eval. rewrite Rows.sum_rows_mod; auto.
        - rewrite weight_value. rewrite <- eval_extend with (n1 := n1); try apply length_small; auto.
        - apply length_small; auto.
        - rewrite extend_length; try apply length_small; auto.
    Qed. *)


    (* Lemma eval_SOS_red_add: forall n1 n2 (v1 : T n1) (v2 : T n2), (n2 <= n1)%nat -> small v1 -> small v2 -> eval (SOS_red_add v1 v2) = eval v1 + eval v2.
    Proof.
      intros. assert (small (SOS_red_add v1 v2)) by (apply small_SOS_red_add; auto). unfold SOS_red_add. unfold SOS_red_add in H2.
      remember (Rows.add weight n1 v1 (Positional.extend_to_length n2 n1 v2)) as v'.
      destruct v'. apply (f_equal (fun y => fst y)) in Heqv'. rewrite Rows.add_partitions in Heqv'; auto.
      simpl in Heqv'. unfold small in H2. 
    Admitted. *)
    
    Local Opaque T addT drop_high_addT' divmod zero scmul conditional_sub sub_then_maybe_add.
    Create HintDb push_mont_eval discriminated.
    Create HintDb word_by_word_montgomery.
    Let r_big' := r_big. (* to put it in the context *)
    Local Ltac t_small :=
      repeat first [ assumption
                   | apply small_addT
                   | apply small_drop_high_addT'
                   | apply small_div
                   | apply small_zero
                   | apply small_scmul
                   | apply small_conditional_sub
                   | apply small_sub_then_maybe_add
                   | apply Z_mod_lt
                   | rewrite Z.mul_split_mod
                   | solve [ auto with zarith ]
                   | lia
                   | progress autorewrite with push_mont_eval
                   | progress autounfold with word_by_word_montgomery
                   | match goal with
                     | [ H : and _ _ |- _ ] => destruct H
                     end ].
    Hint Rewrite
         eval_zero
         eval_div
         eval_mod
         eval_addT
         eval_drop_high_addT'
         eval_scmul
         eval_conditional_sub
         eval_sub_then_maybe_add
         using (repeat autounfold with word_by_word_montgomery; t_small)
      : push_mont_eval.

    Local Arguments eval {_} _.
    Local Arguments small {_} _.
    Local Arguments divmod {_} _.

  Section mul_iteration_proofs.
    Context (pred_A_numlimbs : nat)
    (A : T (S pred_A_numlimbs))
    (small_A : small A).
    (* (S_nonneg : 0 <= eval S). *)

    Local Notation s := (@s pred_A_numlimbs A).
    Local Notation A' := (@A' pred_A_numlimbs A).
    Local Notation thism := (@thism pred_A_numlimbs B A S).
    Local Notation q := (@q pred_A_numlimbs B A S).
    Local Notation S1 := (@S1 pred_A_numlimbs B A S).
    Local Notation S2 := (@S2 pred_A_numlimbs B A S).

End mul_iteration_proofs.

Section red_body_proofs.
    Context (pred_A_numlimbs : nat)
        (N_numlimbs : nat)
        (A : T (S pred_A_numlimbs))
        (small_A : @small (S pred_A_numlimbs) A)
        (A_len : length A = S pred_A_numlimbs)
        (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
        (N_len : length N = R_numlimbs)
        (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs).

        Local Notation red_steps A := (@red_steps pred_A_numlimbs A k).

        Lemma A_bounds: 0 <= eval A.
        Proof.
          apply small_bound; auto.
        Qed.

        Lemma q_bounds: 0 <= eval (q (pred_A_numlimbs) A k).
        Proof.
          apply small_bound; unfold q; apply small_scmul; auto; unfold thism; rewrite Z.mul_split_mod; auto with zarith.
        Qed.
        
        Lemma smallthism: sc_small (thism pred_A_numlimbs A k).
        Proof. clear small_A A_len; unfold thism; rewrite Z.mul_split_mod; unfold sc_small; auto with zarith. Qed. 

        Lemma smallq: small (q pred_A_numlimbs A k).
        Proof. unfold q; apply small_scmul; auto; apply smallthism. Qed.
        Lemma smallS1 : small (S1 pred_A_numlimbs A k).
        Proof. clear A_len; apply small_SOS_red_add; auto with zarith; apply small_scmul; auto; apply smallthism. Qed.

        Lemma div_monot: forall a b c, 0 <= c -> a <= b -> a / c <= b / c.
        Proof.
          intros. apply Z.div_le_mono_nonneg; auto.
        Qed. 

        Local Open Scope Z_scope.
        Lemma div_bound_aux: forall a b d, 0 < d -> b < d -> (a + b)/ d <= a / d + 1.
        Proof. clear A_len A_big small_A.
          intros. assert (a + b <= a + d) by lia; apply div_monot with (c := d) in H1; auto; try lia.
          assert (a + d = a + d * 1) by auto with zarith; rewrite H2 in H1; rewrite Z.div_add' in H1; auto with zarith.
        Qed.

Lemma red_body_bounds: (S R_numlimbs < pred_A_numlimbs)%nat ->  (eval (red_steps A)) / (weight (Nat.pred pred_A_numlimbs)) <= (eval A) / (weight (pred_A_numlimbs)) + 1.
Proof. pose proof smallq as Hq. intros H''.
  destruct pred_A_numlimbs eqn:eq'; auto with zarith.
  rewrite red_steps'. unfold S2. rewrite eval_div; try apply smallS1.
  rewrite Zdiv_Zdiv; try lia; simpl.
  pose proof (weight_value (S n)). rewrite Nat2Z.inj_succ in H. rewrite Z.pow_succ_r in H.
  rewrite H. rewrite weight_value. simpl.
  unfold S1. rewrite eval_SOS_add_full'; auto with zarith.
  destruct (eval A + eval (q (S n) A k) <? (weight (S (S n)))) eqn:eq1.
    - apply Z.ltb_lt in eq1. rewrite (Zdiv_small _ (weight _)).
      + rewrite Z.mul_0_r. rewrite Z.sub_0_r. rewrite weight_value in eq1. rewrite Nat2Z.inj_succ in eq1.
        rewrite Z.pow_succ_r in eq1; try lia.
        apply div_bound_aux.
        apply Z.mul_pos_pos. lia. unfold r. rewrite <- Z.pow_mul_r; auto with zarith.
        apply small_bound in Hq. rewrite weight_value in Hq. rewrite Nat2Z.inj_succ in Hq. rewrite Z.pow_succ_r in Hq; try lia.
        apply lt_S_n in H''.
        assert (r * r ^ (Z.of_nat R_numlimbs) <= r * r ^ (Z.of_nat n)).
        apply Z.mul_le_mono_pos_l; try lia. apply Zpow_facts.Zpower_le_monotone; try lia.
        lia.
      + split; auto. 
        assert (small (q (S n) A k)) by (unfold q; apply small_scmul; auto; unfold thism; rewrite Z.mul_split_mod; auto with zarith).
        apply Z.add_nonneg_nonneg; (apply small_bound; auto).
    - Search (_ <? _ = false). apply Z.ltb_nlt in eq1. Search (?n1 <= ?n2).
      assert (((eval A + eval (q (S n) A k)) / weight (S (S n))) = 1).
        + apply Z.le_antisymm.
          * apply small_carry; auto; lia.
          * Search (0 < (_ / _)). Search ((_ + 1) <= _). assert (1 = 0 + 1) by auto. rewrite H0.
            apply Ztac.Zlt_le_add_1. apply Z.div_str_pos. Search (~ (_ < _)). apply Z.nlt_ge in eq1.
            split; try lia. apply wprops.
        + rewrite H0. pose proof (small_bound Hq). rewrite Z.add_1_r.
          Search ( _ <= Z.succ _). apply Z.le_succ_r; left. apply div_monot; try lia.
          apply Z.mul_nonneg_nonneg; try apply Z.pow_nonneg; lia.
          rewrite Z.mul_1_r. assert (weight (S R_numlimbs) <= weight (S (S n))). apply weight_geq'; lia.
          lia.
    - lia.
    - pose proof wprops as Hw; destruct Hw. pose proof (weight_positive n); lia.
    - unfold S1. apply small_SOS_red_add; auto; try lia.
Qed.

(* Lemma red_body_bounds_final. (S R_numlimbs = pred_A_numlimbs)%nat ->  (eval (red_steps A)) / (weight (Nat.pred pred_A_numlimbs)) <= (eval A) / (weight (pred_A_numlimbs)) + 1.
           *)



End red_body_proofs.


Section red_body_proofs.
      Context (pred_A_numlimbs : nat)
              (N_numlimbs : nat)
              (A : T (S pred_A_numlimbs))
              (small_A : small A)
              (A_len : length A = S pred_A_numlimbs)
              (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
              (N_len : length N = R_numlimbs)
              (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs).

    Local Notation red_body := (@red_body k).
    Local Notation red_loop := (@red_loop N_numlimbs k).

    Let A_s := divmod A.
    Let A' := fst A_s.
    Let s := snd A_s.

    Lemma unfold_A : A = s :: A'.
    Proof. subst s. simpl. subst A'. subst A_s. rewrite <- (undo_div _ _); auto. rewrite A_len. auto. Qed.  

    
  Lemma small_red_body: small (red_body A).
  Proof. 
    unfold red_body. rewrite red_steps'. rewrite unfold_A.
    unfold S2. Check S1. pose proof (small_div ( pred_A_numlimbs) (S1 pred_A_numlimbs (s :: A') k)).
    apply H. unfold S1. apply small_SOS_red_add. lia.
    rewrite <- unfold_A. auto.
    unfold q. apply small_scmul. auto.
    unfold thism. auto.
      - rewrite Z.mul_split_mod. apply Z_mod_lt. lia.
      - auto.
  Qed.

   (* Lemma eval_red_body_mod: r * eval (red_body A) mod eval N = (eval A) mod eval N.
  Proof.
    unfold red_body. rewrite red_steps'. unfold S2.
    rewrite eval_div. Search (?n1 * (_ / ?n1)). rewrite Z.mul_div_eq_full.
    rewrite S1_mod_r. rewrite Z.sub_0_r.
    unfold S1. rewrite eval_SOS_add_full'.

    apply (f_equal (fun (y : Z) => (y / r) mod eval N)).
    unfold S1.  *)


  (* Lemma eval_red_body: eval (red_body A) = (eval A + (eval N) * ((s * k) mod r)) / r.
  Proof.
    unfold red_body. rewrite red_steps'. unfold S2.
    rewrite eval_div. apply (f_equal (fun (y : Z) => (y / r))).
    unfold S1.
    rewrite eval_SOS_red_add.  apply (f_equal (fun y => eval A + y)). unfold q.
    rewrite eval_scmul. rewrite Z.mul_comm. apply (f_equal (fun y => eval N * y)).
    unfold thism. rewrite Z.mul_split_mod.
    all: auto.
      - unfold thism. rewrite Z.mul_split_mod. apply Z_mod_lt. lia.
      - lia.
      - unfold q. apply small_scmul; auto. unfold thism. rewrite Z.mul_split_mod. apply Z_mod_lt. lia.
      - unfold S1. apply small_SOS_red_add; auto; try lia. unfold q. apply small_scmul; auto.
        unfold thism. rewrite Z.mul_split_mod. apply Z_mod_lt. lia.
  Qed. *)

  Lemma divmod_A: eval A mod r = s.
    unfold s, A_s. rewrite eval_mod. auto. auto.
  Qed.

  (* Lemma eval_red_body_mul_r: r * eval (red_body A) = (eval A + (eval N) * ((s * k) mod r)).
  Proof.
    rewrite eval_red_body. Search ((_ / _) * _). rewrite Z.mul_div_eq.
    assert ((eval A + eval N * ((s * k) mod r)) mod r = 0).
      - Search ((_ + _) mod _). rewrite Z.add_mod_full.
        rewrite divmod_A. rewrite Z.mul_mod_full. rewrite Zmod_mod. rewrite <- (Z.mul_comm k).
        rewrite <- Z.mul_mod_full. rewrite Z.mul_assoc. rewrite Z.mul_mod_full.
        rewrite (Z.mul_comm _ k). rewrite k_correct. rewrite <- Z.mul_mod_full.
        rewrite <- Zplus_mod_idemp_l. rewrite <- Z.add_mod_full.
        Search (_ + ( - _)). rewrite Z.add_opp_diag_r. auto with zarith.
      - rewrite H. auto with zarith.
      - lia. 
  Qed. *)

  Lemma div_nil: forall n, @divmod n [] = ([], 0).
  Proof. reflexivity. Qed.

  Lemma div_app: forall n v a, @divmod n (a :: v) = (v, a).
  Proof. reflexivity. Qed.


  Lemma length_div: forall n v, length (fst (@divmod n v)) = Nat.pred (length v).
  Proof. destruct v; simpl; [rewrite (div_nil n)| rewrite (div_app n v z)]; auto. Qed.


  Lemma length_red_body: length (red_body A) = pred_A_numlimbs.
  Proof.
    unfold red_body. rewrite red_steps'. unfold S2. rewrite length_div.
    unfold S1. rewrite length_SOS_red_add; auto with zarith.
    unfold q. rewrite length_sc_mul; auto with zarith.
  Qed.

  End red_body_proofs.

  Section red_loop_proofs.
  Context (pred_A_numlimbs : nat)
  (N_numlimbs : nat)
  (N_len : length N = R_numlimbs)
  (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
  (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs).
  
Definition first_n {n2} n1 : T (n2) -> T n1
:= fun A => firstn n1 A.

Check red_loop.
Check first_n.

  Local Notation red_body := (@red_body k).
  Local Notation red_loop N_num := (@red_loop N_num k).

  Lemma red_loop_next: forall count init A, red_loop init (S count) A = red_loop init count (red_body (A)).
  Proof. intros. auto. Qed.

  Lemma red_loop_comm: forall count init A, red_body (red_loop (S init) count A) = red_loop init count (red_body A).
  Proof.
   intros. generalize dependent A. induction count.
     - intros. simpl. rewrite Nat.add_0_r. auto.
     - intros. pose proof (red_loop_next). rewrite (H count). remember (red_body A) as A'.
       remember (IHcount A'). repeat rewrite <- Nat.add_succ_comm. repeat rewrite <- Nat.add_succ_comm in e. Set Printing All. destruct Heqe. rewrite HeqA' in e. simpl in e.
       Set Printing All. rewrite Nat.add_0_r. repeat rewrite <- Nat.add_succ_comm in e.
       rewrite Nat.add_0_r in e. rewrite e.
       rewrite H. rewrite HeqA'. Set Printing All. repeat rewrite Nat.add_succ_comm.
       repeat rewrite Nat.add_0_r. auto.
  Qed.

  Lemma red_loop_next': forall count init A, red_loop init (S count) (A) = red_body (red_loop (S init) count A).
  Proof.
    intros. rewrite red_loop_comm. auto.
  Qed.

  Lemma small_red_loop: forall init count (A : T (init + count + 1)), small A -> (R_numlimbs <= init)%nat -> (length (A) = init + count + 1)%nat -> small (red_loop (init) count A).
  Proof. clear A_big.
    intros. generalize dependent init. induction count.
      - intros. unfold red_loop. simpl. Set Printing All. rewrite Nat.add_0_r in H. auto.
      - intros. rewrite red_loop_next. apply (IHcount). apply small_red_body.
        + Set Printing All. repeat rewrite <- Nat.add_succ_comm. Search (S (_ + _)). rewrite NPeano.Nat.add_succ_l.
        repeat rewrite <- Nat.add_succ_comm in H. rewrite NPeano.Nat.add_succ_l in H.
        auto.
        + auto with zarith.
        + lia.
        + auto.
        + lia.
        + lia.
        + rewrite length_red_body; auto with zarith.
  Qed.

  Lemma length_red_loop: forall init count A, (R_numlimbs <= init)%nat -> (length A = init + count + 1)%nat -> length (red_loop init count A) = (init + 1)%nat.
  Proof. clear A_big. intros. generalize dependent A. generalize dependent init. induction count.
    - intros. unfold red_loop. simpl. auto with zarith.
    - intros. rewrite red_loop_next'. rewrite length_red_body; auto with zarith.
      + rewrite (IHcount (S init)). auto. auto with zarith. lia.
      + rewrite <- Nat.add_succ_comm. lia.
  Qed. 

  End red_loop_proofs.

  Section red_loop_proofs'.
  Context (pred_A_numlimbs : nat)
          (N_numlimbs : nat)
          (N_len : length N = R_numlimbs)
          (A_big : (R_numlimbs <= pred_A_numlimbs)%nat)
          (N_eval: 0 <= eval N < r ^ Z.of_nat R_numlimbs)
          (A : T (R_numlimbs + R_numlimbs))
          (A_bound : eval A < eval N * eval N)
          (A' : T (S (R_numlimbs + R_numlimbs)) := Positional.extend_to_length (R_numlimbs + R_numlimbs) (S (R_numlimbs + R_numlimbs)) A)
          (A_small: small A).

  Definition A_it (iterations : nat) := red_loop (R_numlimbs + R_numlimbs - iterations) k iterations A'.        

Check A_it.

  Lemma small_A': small A'.
  Proof. unfold A'. apply small_exten; auto. Qed.

  Lemma small_A_it : forall it, (it <= R_numlimbs)%nat -> small (A_it it).
  Proof.
    intros. unfold A_it. apply small_red_loop. all: (auto with zarith; try lia).
    Search Positional.extend_to_length. assert (S (R_numlimbs + R_numlimbs) = (R_numlimbs + R_numlimbs - it + it + 1)%nat). auto with zarith.
    rewrite <- H0. apply small_exten. lia. auto.
    apply length_small in A_small. unfold A'. rewrite extend_length; auto with zarith.
  Qed.

  (* Lemma red_loop_bound_N: forall it, (0 < it <= R_numlimbs)%nat ->
  eval (A_it it) < eval N * r ^ (Z.of_nat (R_numlimbs - it)) + eval N.
  Proof.
    intros. destruct it; try (exfalso; apply (Nat.lt_irrefl O); lia).
    induction it.
      - unfold A_it. simpl. unfold red_body. rewrite red_steps'.
        unfold S2. rewrite Nat.add_0_r. assert (forall y, 0 < y -> y + y -1 + 1 = y + y)%nat by auto with zarith.
        rewrite H0; try lia. rewrite eval_div. Search ( (_ * ?n1) / ?n1). Search (_ < _).
        assert (forall y, y = Z.succ (y - 1)) by auto with zarith.
        rewrite (H1 (_ + eval N)).
        apply Zle_lt_succ.
        rewrite <- (Z_div_mult (_ -1) r). Search ( (_ / ?n1) <= (_ / ?n1)).
        apply div_monot; try lia. unfold S1.
        assert (eval (SOS_red_add A' (q (R_numlimbs + R_numlimbs) A' k)) <= eval A' + eval (q (R_numlimbs + R_numlimbs) A' k)).
        {
          apply eval_SOS_bound; try lia; try apply small_A'. unfold q.
          apply small_scmul; auto; apply smallthism'.
        }
        rewrite Z.mul_sub_distr_r. rewrite Z.mul_1_l.
        rewrite Z.mul_add_distr_r.
        rewrite <- Z.mul_assoc. rewrite (Z.mul_comm _ r).
        rewrite <- Z.pow_succ_r. rewrite <- Nat2Z.inj_succ.
        assert (S (R_numlimbs - 1) = R_numlimbs) by auto with zarith. rewrite H2.
        assert (eval A' < eval N * r ^ Z.of_nat R_numlimbs - r).
        {
          unfold A'. rewrite <- eval_extend. pose proof (small_bound A_small).
          pose proof (small_bound small_N). destruct H5. rewrite (H1 (weight _)) in H6.
          apply Z.lt_succ_r in H6. assert (eval N * eval N <= (weight R_numlimbs - 1) * (weight R_numlimbs - 1)).
          Search (_ * _ <= _ * _). apply Z.mul_le_mono_nonneg; auto; try lia.
          rewrite Z.mul_sub_distr_l in H7. repeat rewrite Z.mul_sub_distr_r in H7.
          repeat rewrite Z.mul_1_r in H7. rewrite Z.mul_1_l in H7. Search (_ - (_ - _)).
          rewrite Z.sub_sub_distr in H7. Search (_ - _ = 0).
          assert (forall y, y + 1 = Z.succ y) by auto.
          assert (weight R_numlimbs * weight R_numlimbs - weight R_numlimbs -
          weight R_numlimbs + 1 <)
          
          rewrite H8 in H7.
          apply Z.lt_succ_r in H7.
          
          
          
          rewrite weight_value in H4.
          assert (eval N * eval N < eval N * r ^ Z.of_nat R_numlimbs) by (apply Zmult_gt_0_lt_compat_l; try lia).
          lia. lia. apply length_small; auto.
        }
        assert (eval (q (R_numlimbs + R_numlimbs) A' k) < eval N * r).
        {
          unfold q. rewrite eval_scmul. pose proof (smallthism' (R_numlimbs + R_numlimbs) A').
          unfold sc_small in H4. rewrite Z.mul_comm. apply Zmult_gt_0_lt_compat_l; try lia.
          all: auto. apply smallthism'.
        }
        lia. lia. lia.
        unfold S1. apply small_SOS_red_add; try lia. apply small_A'. unfold q. apply small_scmul; auto. apply smallthism'.
      - remember (S it) as it'. unfold A_it in IHit.
        assert (HZ: (R_numlimbs + R_numlimbs - it' + it' + 1)%nat = (S (R_numlimbs + R_numlimbs))%nat) by auto with zarith.
        assert (S (R_numlimbs + R_numlimbs - (S it')) = R_numlimbs + R_numlimbs - it')%nat by auto with zarith.
        unfold A_it. rewrite red_loop_next'. repeat rewrite Nat.add_1_r. unfold red_body.
        rewrite red_steps'. unfold S2. rewrite eval_div. rewrite H0. unfold S1.

        assert ( eval
        (SOS_red_add (red_loop (R_numlimbs + R_numlimbs - it') k it' A')
           (q (R_numlimbs + R_numlimbs - it')
              (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k)) 
          <= eval (red_loop (R_numlimbs + R_numlimbs - it') k it' A') + eval (q (R_numlimbs + R_numlimbs - it')
          (red_loop (R_numlimbs + R_numlimbs - it') k it' A') k)).
          apply eval_SOS_bound; try lia.
          + apply small_red_loop; try lia. rewrite HZ. apply small_A'.
            rewrite HZ. apply length_small. apply small_A'.
          + unfold q; apply small_scmul; auto; apply smallthism'.
          + rewrite <- (Z_div_mult (_ + eval N) r).
            (* apply div_monot; try lia. *)
            rewrite Z.mul_add_distr_r. rewrite <- Z.mul_assoc.
            assert (r ^ Z.of_nat (R_numlimbs - S it') * r = r ^ Z.of_nat (R_numlimbs - it')).
            {
              rewrite Z.mul_comm. rewrite <- Z.pow_succ_r. rewrite <- Nat2Z.inj_succ.
              assert (S (R_numlimbs - S it') = R_numlimbs - it')%nat by auto with zarith.
              rewrite H2. auto. lia.
            }
            rewrite H2.
            assert (0 < it' <= R_numlimbs)%nat by lia.
            remember (IHit H3) as H4. destruct HeqH4.
            Search ( (_ + _ * ?n1) / ?n1). rewrite Z_div_plus_full; auto with zarith.

            apply (div_monot _ _ r) in H4.
            assert (R_numlimbs - it' = 1)%nat. rewrite by auto with zarith.
            
            assert (eval (red_loop (R_numlimbs + R_numlimbs - it') k it' A') < eval N * r ^ (Z.of_nat (R_numlimbs - it'))).
          
          assert (eval)
        
        assert (eval (S1 (R_numlimbs + R_numlimbs) A' k) < eval N * r ^ (Z.of_nat))
        
        
        pose proof (eval_div R_numlimbs + R_numlimbs).
        Set Printing All. rewrite Nat.add_1_r.
        Set Printing All. repeat rewrite Nat.sub_0_r. rewrite <- H0.
 *)

  Lemma red_loop_it: forall it, (it < R_numlimbs)%nat -> eval (A_it it) / weight (R_numlimbs + R_numlimbs - it) <= Z.of_nat it.
  Proof.
    intros it H'. induction it.
      - unfold A_it. unfold red_loop. simpl. assert (small A') by (apply small_exten; auto; try lia).
        Search (_ / _ = 0). rewrite Zdiv_small; auto with zarith. unfold A'.
        rewrite Nat.sub_0_r. rewrite Nat.add_1_r.
        rewrite <- eval_extend. apply small_bound in A_small. auto. lia.
        apply length_small in A_small. auto.
      - unfold A_it. unfold A_it in IHit. rewrite red_loop_next'.
        assert (S (R_numlimbs + R_numlimbs - S it) = R_numlimbs + R_numlimbs - it)%nat by auto with zarith.
        rewrite H.
        remember (red_loop (R_numlimbs + R_numlimbs - it) k it A') as A''.
        assert (eval (red_body k (red_loop (S (R_numlimbs + R_numlimbs - S it)) k it A')) /
        weight (R_numlimbs + R_numlimbs - S it) <= eval A'' / weight (R_numlimbs + R_numlimbs - it) + 1).
          {
             rewrite H. rewrite <- HeqA''. Check red_body. unfold red_body.
             pose proof (red_body_bounds (R_numlimbs + R_numlimbs - it) A'').
             rewrite Nat.add_1_r. assert (R_numlimbs + R_numlimbs - S it = Nat.pred (R_numlimbs + R_numlimbs - it))%nat by auto with zarith.
             rewrite H1. Search (S (Nat.pred _)). rewrite NPeano.Nat.succ_pred_pos; try lia.
             rewrite Nat.add_1_r. apply H0. pose proof (length_small small_N).
             rewrite HeqA''. assert (0 <= eval N < r ^ Z.of_nat R_numlimbs) by auto.
             pose proof (small_red_loop H2 H3 (R_numlimbs + R_numlimbs - it) it A').
            repeat rewrite Nat.add_1_r in H4. apply H4. assert (S (R_numlimbs + R_numlimbs - it + it) = S (R_numlimbs + R_numlimbs)). auto with zarith.
            rewrite H5. apply small_A'.
            all: auto with zarith; try lia.
            unfold A'. Search Positional.extend_to_length. rewrite extend_length; auto with zarith; try lia.
            pose proof (length_small A_small). auto.
            rewrite HeqA''. pose proof (length_small small_N).
            pose proof (length_red_loop H2 (R_numlimbs + R_numlimbs - it) it A').
            repeat rewrite Nat.add_1_r in H3. apply H3; try lia.
            unfold A'. assert (S (R_numlimbs + R_numlimbs - it + it) = S (R_numlimbs + R_numlimbs)) by auto with zarith.
            rewrite H4. apply extend_length; auto; try lia. apply length_small; auto. 
          }
        assert (S (R_numlimbs + R_numlimbs - S it)= R_numlimbs + R_numlimbs - it)%nat by auto with zarith.
        rewrite H1 in H0. rewrite <- HeqA'' in H0.
        repeat rewrite Nat.add_1_r. repeat rewrite Nat.add_1_r in H0.
        repeat rewrite Nat.add_1_r in IHit. assert (it < R_numlimbs)%nat by lia.
        apply IHit in H2. lia.
  Qed.

  Lemma add_small_it: forall it, (it < R_numlimbs)%nat -> eval (A_it it) + eval (q (R_numlimbs + R_numlimbs - it) (A_it it) k)
    < weight (S (R_numlimbs + R_numlimbs - it)).
  Proof. intros. (*remove these pose proofs*) pose proof Z.add_0_r. pose proof Z.add_0_l. 
    pose proof (red_loop_it it). assert (it < R_numlimbs)%nat by lia.
    apply H2 in H3.
    Search (_ * ?n1 <= _ * ?n1). apply (Z.mul_le_mono_pos_r _ _ (weight (R_numlimbs + R_numlimbs - it))) in H3.
    Search (_ / _). rewrite Z.mul_comm in H3. rewrite Z.mul_div_eq_full in H3.
    Search (_ + ?n1 <= _ + ?n1).
    apply (Z.add_le_mono_r _ _ (eval (A_it it) mod weight (R_numlimbs + R_numlimbs - it))) in H3.
    simpl in H3. Search (_ - ?n1 + ?n1 = _). rewrite Z.sub_add in H3.
    assert (eval (A_it it) mod weight (R_numlimbs + R_numlimbs - it) < weight (R_numlimbs + R_numlimbs - it)). Search (_ mod _ < _).
    apply Z.mod_bound_pos. apply small_bound. rewrite Nat.add_1_r. auto.
    unfold A_it. pose proof (length_small small_N) as HN.
    pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
    pose proof (small_red_loop HN HN' (R_numlimbs + R_numlimbs - it) it A').
    repeat rewrite Nat.add_1_r in H4. apply H4. pose proof small_A'.
    assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
    rewrite H6. auto. lia.
    assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
    rewrite H5. apply length_small. apply small_A'. auto with zarith.
    assert ( (Z.of_nat it) * weight (R_numlimbs + R_numlimbs - it) + eval (A_it it) mod weight (R_numlimbs + R_numlimbs - it) < (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it)) by lia.
    assert (eval (A_it it) <=  (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it)) by lia.
    assert (small (q (R_numlimbs + R_numlimbs - it)
    (red_loop (R_numlimbs + R_numlimbs - it) k it A') k)).
      * unfold q. apply small_scmul; auto; apply smallthism'.
      * apply small_bound in H7.
      assert (weight (S R_numlimbs) + (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it) <= weight (S (R_numlimbs + R_numlimbs - it))).
      {
        repeat rewrite weight_value.
        assert (Z.of_nat it + 1 <= r - 1). lia. 
        assert ((Z.of_nat it + 1) * r ^ Z.of_nat (R_numlimbs + R_numlimbs - it) <= (r - 1) * r ^ Z.of_nat ((R_numlimbs + R_numlimbs - it))).
        Search ( (_ + _) * _).
        Search ( _ * _ <= _ * _).
        Set Printing All. apply Z.mul_le_mono_nonneg_r. assert (O < R_numlimbs + R_numlimbs - it)%nat by lia.
        unfold r. Search (0 <= _ ^ _). Search ((_ ^ _) ^ _). rewrite <- Z.pow_mul_r.
        apply Pow2.Z.pow2_ge_0. all: try lia.
        assert (r ^ Z.of_nat (S R_numlimbs) <= r ^ Z.of_nat (R_numlimbs + R_numlimbs - it)).
        Search (_ ^ _ <= _). pose proof (Z.pow_le_mono_r r (Z.of_nat (S R_numlimbs)) (Z.of_nat (R_numlimbs + R_numlimbs - it))).
        apply H10. all: try lia.
        rewrite Z.mul_sub_distr_r in H9. rewrite Z.mul_1_l in H9.
        Search (_ + _ <= _ + _). 
        rewrite (Z.add_le_mono_r _ _ (r ^ Z.of_nat (R_numlimbs + R_numlimbs - it))) in H9.
        Search (_ - ?n1 + ?n1). rewrite Z.sub_add in H9.
        rewrite Z.add_comm in H9. Search (_ ^ (Z.succ _)). rewrite (Nat2Z.inj_succ (R_numlimbs + R_numlimbs - it) ).
        rewrite (Z.pow_succ_r  _ (Z.of_nat (R_numlimbs + R_numlimbs - it))). lia.
        lia.
      }
      unfold A_it in H6. rewrite Z.add_comm in H8.
      assert ( (eval (red_loop (R_numlimbs + R_numlimbs - it) k it A') +
      eval
        (q (R_numlimbs + R_numlimbs - it)
           (red_loop (R_numlimbs + R_numlimbs - it) k it A') k)) < (Z.of_nat it + 1) * weight (R_numlimbs + R_numlimbs - it) +
           weight (S R_numlimbs)). lia. repeat rewrite Nat.add_1_r in H9. unfold A_it.
           lia.
      * auto.
      * rewrite weight_value. unfold r. rewrite <- Z.pow_mul_r.
        Search (0 < _ ^ _). apply Pow2.Z.pow2_gt_0. assert (0 < R_numlimbs + R_numlimbs - it)%nat by lia.
        lia. lia. lia.
  Qed.

  Lemma red_loop_it_mod: forall it, (it < R_numlimbs)%nat -> ((r ^ Z.of_nat it * eval (A_it it) mod eval N)
    = eval A mod eval N).
  Proof.
    intros. assert (Haux: (R_numlimbs + R_numlimbs - it + it)%nat = (R_numlimbs + R_numlimbs)%nat) by auto with zarith.
    assert (small_A_it: small (A_it it)). unfold A_it. apply small_red_loop; auto. 
    rewrite Haux. rewrite Nat.add_1_r. apply small_A'. lia. rewrite Haux. rewrite Nat.add_1_r. apply length_small. apply small_A'. 
     induction it.
      - unfold A_it. unfold red_loop. simpl. Set Printing All. simpl. assert (eval A = eval A'). unfold A'. rewrite <- eval_extend. auto.
      auto. apply length_small. auto. rewrite Nat.sub_0_r. rewrite Nat.add_1_r.
      rewrite H0. 
      Set Printing All.
      
      auto.
      destruct (eval A'); auto.
      - unfold A_it. rewrite red_loop_next'. rewrite r_pow_S.
        assert (it < R_numlimbs)%nat by lia. apply IHit in H0.
         repeat rewrite Nat.add_1_r. unfold red_body. rewrite red_steps'.
         unfold S2. Search (eval (fst (divmod _))). rewrite eval_div.
         rewrite <- Z.mul_assoc. Search (?n1 * (_ / ?n1)).
         rewrite Z.mul_div_eq_full. rewrite S1_mod_r. rewrite Z.sub_0_r.
         unfold A_it in H0. unfold S1. rewrite eval_SOS_add_small.
         unfold q. rewrite eval_scmul. rewrite Z.mul_mod. rewrite Z.add_mod.
         Search ( (_ * ?n1 mod ?n1)). rewrite Z.mod_mul. rewrite Z.add_0_r.
         rewrite <- Z.mod_mod. rewrite <- Z.mul_mod. rewrite Z.mod_mod.
         assert (S (R_numlimbs + R_numlimbs - S it) = (R_numlimbs + R_numlimbs - it))%nat by auto with zarith.
         rewrite H1. 
         Set Printing All. rewrite Nat.add_1_r in H0.
         rewrite Z.mul_mod. rewrite Z.mod_mod. rewrite <- Z.mul_mod. auto.
         all: auto; try lia.
          + apply smallthism'.
          + pose proof (length_small small_N) as HN.
            pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
           pose proof (small_red_loop HN HN' (R_numlimbs + R_numlimbs - it) it A').
          assert (S (R_numlimbs + R_numlimbs - S it) = (R_numlimbs + R_numlimbs - it))%nat by auto with zarith.
          rewrite H2.
           Set Printing All. repeat rewrite Nat.add_1_r in H1. apply H1.
           assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
           rewrite H3. apply small_A'. lia.
           assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
           rewrite H3. apply length_small. apply small_A'.
          + unfold q. apply small_scmul; auto; try lia. apply smallthism'.
          + assert (S (R_numlimbs + R_numlimbs - S it) = (R_numlimbs + R_numlimbs - it))%nat by auto with zarith.
            rewrite H1. pose proof (add_small_it it). unfold A_it in H2.
            rewrite Nat.add_1_r in H2. apply H2. lia.
          + assert (HN: length N = R_numlimbs). apply length_small; auto.
            pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
            pose proof (small_red_loop HN HN' ( (R_numlimbs + R_numlimbs - it)) it). Set Printing All.
            assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S it)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( it)))) by auto with zarith.
            rewrite H2. repeat rewrite Nat.add_1_r in H1.
            Set Printing All.
            apply H1.
            assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
            rewrite H3. apply small_A'. lia.
            assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
            rewrite H3. apply extend_length; auto. apply length_small. auto.
          + unfold S1. apply small_SOS_red_add; try lia.
            assert (HN: length N = R_numlimbs). apply length_small; auto.
            pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
            pose proof (small_red_loop HN HN' ( (R_numlimbs + R_numlimbs - it)) it). Set Printing All.
            assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S it)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( it)))) by auto with zarith.
            rewrite H2. repeat rewrite Nat.add_1_r in H1.
            Set Printing All.
            apply H1.
            assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
            rewrite H3. apply small_A'. lia.
            assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
            rewrite H3. apply extend_length; auto. apply length_small. auto.
            unfold q. apply small_scmul; auto; apply smallthism'.
          + Set Printing All. repeat rewrite Nat.add_1_r.
            unfold A_it.
            assert (HN: length N = R_numlimbs). apply length_small; auto.
            pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
            pose proof (small_red_loop HN HN' ( (R_numlimbs + R_numlimbs - it)) it). Set Printing All.
            assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S it)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( it)))) by auto with zarith.
            repeat rewrite Nat.add_1_r in H1.
            Set Printing All.
            apply H1.
            assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
            rewrite H3. apply small_A'. lia.
            assert (R_numlimbs + R_numlimbs - it + it = R_numlimbs + R_numlimbs)%nat by auto with zarith.
            rewrite H3. apply extend_length; auto. apply length_small. auto.
  Qed.


  Lemma red_loop_final: (r ^ Z.of_nat R_numlimbs) * eval (A_it R_numlimbs) mod eval N = eval A mod eval N.
  Proof.
    unfold A_it. assert (forall (y : nat), y + y - y = y)%nat by auto with zarith. rewrite H.
    assert (exists x, R_numlimbs = S x). apply Nat.neq_0_r. auto. destruct H0.
    assert (eval (red_loop R_numlimbs k R_numlimbs A') = eval (red_loop R_numlimbs k (S x) A')) by (rewrite <- H0; auto).
    rewrite H1. rewrite red_loop_next'. repeat rewrite Nat.add_1_r. unfold red_body.
    rewrite red_steps'. unfold S2. Search (eval (fst (divmod _))). rewrite eval_div.
    unfold S1. rewrite eval_SOS_add_small. assert (r ^ Z.of_nat R_numlimbs = r ^ (Z.of_nat (S x))).
    rewrite H0. auto.
    rewrite H2. rewrite r_pow_S. rewrite <- Z.mul_assoc. Search (?n1 * (_ / ?n1)).
    rewrite Z.mul_div_eq. Search (_ mod r). pose proof S1_mod_r. unfold S1 in H3.
    unfold SOS_red_add in H3. rewrite add_q_low_word.
    rewrite Z.sub_0_r. unfold q. rewrite eval_scmul. Search (_ * (_ + _)).
    rewrite Z.mul_add_distr_l. rewrite Z.add_mod. Search ( _ * ?n1 mod ?n1).
    rewrite Z.mul_assoc. rewrite Z_mod_mult. rewrite Z.add_0_r.
    rewrite Z.mul_mod. rewrite Z.mod_mod. rewrite <- Z.mul_mod.
    assert (x < R_numlimbs)%nat by lia.
    pose proof (red_loop_it_mod x H4). unfold A_it in H5.
    assert (R_numlimbs + R_numlimbs - x = S R_numlimbs)%nat. auto with zarith.
    rewrite H6 in H5. rewrite Nat.add_1_r in H5. 
    apply H5. all: auto with zarith; try lia.
    - apply smallthism'.
    - assert (HN: length N = R_numlimbs). apply length_small; auto.
      pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
      pose proof (small_red_loop HN HN' (S R_numlimbs ) x A'). Set Printing All.
      assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S x)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( x)))) by auto with zarith.
      repeat rewrite Nat.add_1_r in H4. Set Printing All.
      apply H4. pose proof small_A'.
      unfold small. unfold small in H6.
      assert (R_numlimbs + R_numlimbs = S R_numlimbs + x)%nat by auto with zarith.
      rewrite <- H7. auto. lia.
      unfold A'. rewrite extend_length. auto with zarith.
      apply length_small; auto. lia.
    - assert (HN: length N = R_numlimbs). apply length_small; auto.
      pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
      pose proof (small_red_loop HN HN' (S R_numlimbs ) x A'). Set Printing All.
      assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S x)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( x)))) by auto with zarith.
      repeat rewrite Nat.add_1_r in H2. Set Printing All.
      apply H2. pose proof small_A'.
      unfold small. unfold small in H4.
      assert (R_numlimbs + R_numlimbs = S R_numlimbs + x)%nat by auto with zarith.
      rewrite <- H5. auto. lia.
      unfold A'. rewrite extend_length. auto with zarith.
      apply length_small; auto. lia.
    - unfold q. apply small_scmul; auto; apply smallthism'.
    - assert (S R_numlimbs = R_numlimbs + R_numlimbs - x)%nat by auto with zarith.
      repeat rewrite H2. pose proof (add_small_it x). unfold A_it in H3. rewrite Nat.add_1_r in H3.
      rewrite H2 in H3. apply H3. lia.
    - unfold S1. apply small_SOS_red_add; try lia.
      assert (HN: length N = R_numlimbs). apply length_small; auto.
      pose proof (small_bound small_N) as HN'. rewrite weight_value in HN'.
      pose proof (small_red_loop HN HN' (S R_numlimbs ) x A'). Set Printing All.
      assert ((S (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) (S x)) =  (Init.Nat.sub (Init.Nat.add R_numlimbs R_numlimbs) ( x)))) by auto with zarith.
      repeat rewrite Nat.add_1_r in H2. Set Printing All.
      apply H2. pose proof small_A'.
      unfold small. unfold small in H4.
      assert (R_numlimbs + R_numlimbs = S R_numlimbs + x)%nat by auto with zarith.
      rewrite <- H5. auto. lia.
      unfold A'. rewrite extend_length. auto with zarith.
      apply length_small; auto. lia.
      unfold q. apply small_scmul; auto; apply smallthism'.
  Qed.


  (* Lemma eval_red_loop: forall init count (A : T (init + count + 1)), (length A = init + count + 1)%nat -> (R_numlimbs <= init)%nat -> small A -> (eval A) mod eval N = (r ^Z.of_nat count * eval (red_loop init count A)) mod eval N.
  Proof. intros. generalize dependent A. generalize dependent init. induction count.
    - intros. simpl. auto with zarith. Set Printing All. rewrite Nat.add_0_r. auto.
      destruct (eval A) eqn:eq1.
        + repeat rewrite <- Nat.add_succ_comm. repeat rewrite Nat.add_0_r.
          repeat rewrite <- Nat.add_succ_comm in eq1. repeat rewrite Nat.add_0_r in eq1.
          rewrite eq1. auto.
        + repeat rewrite <- Nat.add_succ_comm. repeat rewrite Nat.add_0_r.
          repeat rewrite <- Nat.add_succ_comm in eq1. repeat rewrite Nat.add_0_r in eq1.
          rewrite eq1. auto.
        + repeat rewrite <- Nat.add_succ_comm. repeat rewrite Nat.add_0_r.
          repeat rewrite <- Nat.add_succ_comm in eq1. repeat rewrite Nat.add_0_r in eq1.
          rewrite eq1. auto.
     (* rewrite Z.mod_small. rewrite Z.div_1_r. rewrite Z.mul_0_r. rewrite Z.add_0_r. rewrite Nat.add_1_r.
      auto. Set Printing All. rewrite Nat.add_succ_r. auto.
      + auto. lia. *)
    - intros. rewrite red_loop_next'.
      Search (Z.pow). rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. rewrite (Z.mul_comm (r)).
      rewrite <- Z.mul_assoc.
      rewrite eval_red_body_mul_r. rewrite Z.mul_mod_full.
      rewrite Z.add_mod_full. simpl. rewrite (Z.mul_comm (eval N)).
      Search ((_ * _ mod _ = 0)). rewrite Z_mod_mult. rewrite Z.add_0_r.
      rewrite Zmod_mod. simpl. rewrite <- Z.mul_mod_full. rewrite <- (IHcount (S init)).
      Set Printing All. repeat rewrite Nat.add_succ_comm. Set Printing All. auto.
        + lia.
        + rewrite H. auto with zarith.
        + repeat rewrite Nat.add_succ_comm. auto.
        + apply (small_red_loop (S init)); auto with zarith.
          * repeat rewrite Nat.add_succ_comm. auto.
        + rewrite length_red_loop; auto with zarith.
        + rewrite <- Nat.add_succ_comm. lia.
        + auto.
        + auto.
        + lia.
  Qed. *)
  

  (* Lemma eval_loop_full: forall (A : T (S (R_numlimbs + R_numlimbs))), small A -> length A = S (R_numlimbs + R_numlimbs) -> eval A mod eval N = (r ^ Z.of_nat R_numlimbs) * eval (red_loop R_numlimbs R_numlimbs A) mod eval N.
  Proof. 
    intros. rewrite <- eval_red_loop; repeat rewrite Nat.add_succ_comm; repeat rewrite Nat.add_1_r; auto.
  Qed. *)




  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds
    Section Iteration_proofs.
      Context (pred_A_numlimbs : nat)
              (A : T (S pred_A_numlimbs))
              (S : T (S R_numlimbs))
              (small_A : small A)
              (small_S : small S)
              (S_nonneg : 0 <= eval S).
      (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)

      Local Coercion eval : T >-> Z.

      Local Notation a := (@a pred_A_numlimbs A).
      Local Notation A' := (@A' pred_A_numlimbs A).
      Local Notation S1 := (@S1 pred_A_numlimbs B A S).
      Local Notation s := (@s pred_A_numlimbs B A S).
      Local Notation q := (@q pred_A_numlimbs B k A S).
      Local Notation S2 := (@S2 pred_A_numlimbs B k A S).
      Local Notation S3 := (@S3' pred_A_numlimbs B k A S).

      Local Notation eval_pre_S3 := ((S + a * B + q * N) / r).

      Lemma eval_S3_eq : eval S3 = eval_pre_S3 mod (r * r ^ Z.of_nat R_numlimbs).
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big.
        unfold S3, S2, S1.
        autorewrite with push_mont_eval push_Zof_nat; [].
        rewrite !Z.pow_succ_r, <- ?Z.mul_assoc by lia.
        rewrite Z.mod_pull_div by Z.zero_bounds.
        do 2 f_equal; nia.
      Qed.

      Lemma pre_S3_bound
        : eval S < eval N + eval B
          -> eval_pre_S3 < eval N + eval B.
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big.
        assert (Hmod : forall a b, 0 < b -> a mod b <= b - 1)
          by (intros x y; pose proof (Z_mod_lt x y); lia).
        intro HS.
        eapply Z.le_lt_trans.
        { transitivity ((N+B-1 + (r-1)*B + (r-1)*N) / r);
            [ | set_evars; ring_simplify_subterms; subst_evars; reflexivity ].
          Z.peel_le; repeat apply Z.add_le_mono; repeat apply Z.mul_le_mono_nonneg; try lia;
            repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
              autorewrite with push_mont_eval;
              try Z.zero_bounds;
              auto with lia. }
        rewrite (Z.mul_comm _ r), <- Z.add_sub_assoc, <- Z.add_opp_r, !Z.div_add_l' by lia.
        autorewrite with zsimplify.
        simpl; lia.
      Qed.

      Lemma pre_S3_nonneg : 0 <= eval_pre_S3.
      Proof using N_nz B_bounds small_B small_A small_S S_nonneg lgr_big.
        clear -N_nz B_bounds small_B partition_Proper r_big' small_A small_S S_nonneg.
        repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
          autorewrite with push_mont_eval; [].
        rewrite ?Npos_correct; Z.zero_bounds; lia.
      Qed.

      Lemma small_A'
        : small A'.
      Proof using small_A lgr_big. repeat autounfold with word_by_word_montgomery; t_small. Qed.

      Lemma small_S3
        : small S3.
      Proof using small_A small_S small_N N_lt_R N_nz B_bounds small_B lgr_big.
        clear -small_A small_S small_N N_lt_R N_nz B_bounds small_B partition_Proper r_big'.
        repeat autounfold with word_by_word_montgomery; t_small.
      Qed.

      Lemma S3_nonneg : 0 <= eval S3.
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big sub_then_maybe_add.
        rewrite eval_S3_eq; Z.zero_bounds.
      Qed.

      Lemma S3_bound
        : eval S < eval N + eval B
          -> eval S3 < eval N + eval B.
      Proof using N_nz B_bounds small_B small_A small_S S_nonneg B_bounds N_nz N_lt_R small_N lgr_big.
        clear -N_nz B_bounds small_B small_A small_S S_nonneg B_bounds N_nz N_lt_R small_N lgr_big partition_Proper r_big' sub_then_maybe_add.
        rewrite eval_S3_eq.
        intro H; pose proof (pre_S3_bound H); pose proof pre_S3_nonneg.
        subst R.
        rewrite Z.mod_small by nia.
        assumption.
      Qed.

      Lemma S1_eq : eval S1 = S + a*B.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper.
        cbv [S1 a A'].
        repeat autorewrite with push_mont_eval.
        reflexivity.
      Qed.

      Lemma S2_mod_r_helper : (S + a*B + q * N) mod r = 0.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct.
        cbv [S2 q s]; autorewrite with push_mont_eval; rewrite S1_eq.
        assert (r > 0) by lia.
        assert (Hr : (-(1 mod r)) mod r = r - 1 /\ (-(1)) mod r = r - 1).
        { destruct (Z.eq_dec r 1) as [H'|H'].
          { rewrite H'; split; reflexivity. }
          { rewrite !Z_mod_nz_opp_full; rewrite ?Z.mod_mod; Z.rewrite_mod_small; [ split; reflexivity | lia.. ]. } }
        autorewrite with pull_Zmod.
        replace 0 with (0 mod r) by apply Zmod_0_l.
        pose (Z.to_pos r) as r'.
        replace r with (Z.pos r') by (subst r'; rewrite Z2Pos.id; lia).
        eapply F.eq_of_Z_iff.
        rewrite Z.mul_split_mod.
        repeat rewrite ?F.of_Z_add, ?F.of_Z_mul, <-?F.of_Z_mod.
        rewrite <-!Algebra.Hierarchy.associative.
        replace ((F.of_Z r' k * F.of_Z r' (eval N))%F) with (F.opp (m:=r') F.one).
        { cbv [F.of_Z F.add]; simpl.
          apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ].
          simpl.
          subst r'; rewrite Z2Pos.id by lia.
          rewrite (proj1 Hr), Z.mul_sub_distr_l.
          push_Zmod; pull_Zmod.
          apply (f_equal2 Z.modulo); lia. }
        { rewrite <- F.of_Z_mul.
          rewrite F.of_Z_mod.
          subst r'; rewrite Z2Pos.id by lia.
          rewrite k_correct.
          cbv [F.of_Z F.add F.opp F.one]; simpl.
          change (-(1)) with (-1) in *.
          apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ]; simpl.
          rewrite Z2Pos.id by lia.
          rewrite (proj1 Hr), (proj2 Hr); Z.rewrite_mod_small; reflexivity. }
      Qed.

      Lemma pre_S3_mod_N
        : eval_pre_S3 mod N = (S + a*B)*ri mod N.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct ri_correct.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct ri_correct sub_then_maybe_add.
        pose proof fun a => Z.div_to_inv_modulo N a r ri ltac:(lia) ri_correct as HH;
                              cbv [Z.equiv_modulo] in HH; rewrite HH; clear HH.
        etransitivity; [rewrite (fun a => Z.mul_mod_l a ri N)|
                        rewrite (fun a => Z.mul_mod_l a ri N); reflexivity].
        rewrite S2_mod_r_helper.
        push_Zmod; pull_Zmod; autorewrite with zsimplify_const.
        reflexivity.
      Qed.

      Lemma S3_mod_N
            (Hbound : eval S < eval N + eval B)
        : S3 mod N = (S + a*B)*ri mod N.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct ri_correct small_N N_lt_R N_nz S_nonneg.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct ri_correct N_nz N_lt_R small_N sub_then_maybe_add Hbound S_nonneg.
        rewrite eval_S3_eq.
        pose proof (pre_S3_bound Hbound); pose proof pre_S3_nonneg.
        rewrite (Z.mod_small _ (r * _)) by (subst R; nia).
        apply pre_S3_mod_N.
      Qed.
    End Iteration_proofs.

    Section redc_proofs.
      Local Notation redc_body := (@redc_body B k).
      Local Notation redc_loop := (@redc_loop B k).
      Local Notation pre_redc A := (@pre_redc _ A B k).
      Local Notation redc A := (@redc _ A B k).

      Section body.
        Context (pred_A_numlimbs : nat)
                (A_S : T (S pred_A_numlimbs) * T (S R_numlimbs)).
        Let A:=fst A_S.
        Let S:=snd A_S.
        Let A_a:=divmod A.
        Let a:=snd A_a.
        Context (small_A : small A)
                (small_S : small S)
                (S_bound : 0 <= eval S < eval N + eval B).

        Lemma small_fst_redc_body : small (fst (redc_body A_S)).
        Proof using S_bound small_A small_S lgr_big. destruct A_S; apply small_A'; assumption. Qed.
        Lemma small_snd_redc_body : small (snd (redc_body A_S)).
        Proof using small_S small_N small_B small_A lgr_big S_bound B_bounds N_nz N_lt_R.
          destruct A_S; unfold redc_body; apply small_S3; assumption.
        Qed.
        Lemma snd_redc_body_nonneg : 0 <= eval (snd (redc_body A_S)).
        Proof using small_S small_N small_B small_A lgr_big S_bound N_nz N_lt_R B_bounds.
          destruct A_S; apply S3_nonneg; assumption.
        Qed.

        Lemma snd_redc_body_mod_N
          : (eval (snd (redc_body A_S))) mod (eval N) = (eval S + a*eval B)*ri mod (eval N).
        Proof using small_S small_N small_B small_A ri_correct lgr_big k_correct S_bound R_numlimbs_nz N_nz N_lt_R B_bounds.
          clear -small_S small_N small_B small_A ri_correct k_correct S_bound R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add r_big' partition_Proper.
          destruct A_S; apply S3_mod_N; auto; lia.
        Qed.

        Lemma fst_redc_body
          : (eval (fst (redc_body A_S))) = eval (fst A_S) / r.
        Proof using small_S small_A S_bound lgr_big.
          destruct A_S; simpl; repeat autounfold with word_by_word_montgomery; simpl.
          autorewrite with push_mont_eval.
          reflexivity.
        Qed.

        Lemma fst_redc_body_mod_N
          : (eval (fst (redc_body A_S))) mod (eval N) = ((eval (fst A_S) - a)*ri) mod (eval N).
        Proof using small_S small_A ri_correct lgr_big S_bound.
          clear R_numlimbs_nz.
          rewrite fst_redc_body.
          etransitivity; [ eapply Z.div_to_inv_modulo; try eassumption; lia | ].
          unfold a, A_a, A.
          autorewrite with push_mont_eval.
          reflexivity.
        Qed.

        Lemma redc_body_bound
          : eval S < eval N + eval B
            -> eval (snd (redc_body A_S)) < eval N + eval B.
        Proof using small_S small_N small_B small_A lgr_big S_bound N_nz N_lt_R B_bounds.
          clear -small_S small_N small_B small_A S_bound N_nz N_lt_R B_bounds r_big' partition_Proper sub_then_maybe_add.
          destruct A_S; apply S3_bound; unfold S in *; cbn [snd] in *; try assumption; try lia.
        Qed.
      End body.

      Local Arguments Z.pow !_ !_.
      Local Arguments Z.of_nat !_.
      Local Ltac induction_loop count IHcount
        := induction count as [|count IHcount]; intros; cbn [redc_loop nat_rect] in *; [ | (*rewrite redc_loop_comm_body in * *) ].
      Lemma redc_loop_good count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : (small (fst (redc_loop count A_S)) /\ small (snd (redc_loop count A_S)))
          /\ 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        induction_loop count IHcount; auto; [].
        change (id (0 <= eval B < R)) in B_bounds (* don't let [destruct_head'_and] loop *).
        destruct_head'_and.
        repeat first [ apply conj
                     | apply small_fst_redc_body
                     | apply small_snd_redc_body
                     | apply redc_body_bound
                     | apply snd_redc_body_nonneg
                     | apply IHcount
                     | solve [ auto ] ].
      Qed.

      Lemma small_redc_loop count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : small (fst (redc_loop count A_S)) /\ small (snd (redc_loop count A_S)).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds. apply redc_loop_good; assumption. Qed.

      Lemma redc_loop_bound count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds. apply redc_loop_good; assumption. Qed.

      Local Ltac handle_IH_small :=
        repeat first [ apply redc_loop_good
                     | apply small_fst_redc_body
                     | apply small_snd_redc_body
                     | apply redc_body_bound
                     | apply snd_redc_body_nonneg
                     | apply conj
                     | progress cbn [fst snd]
                     | progress destruct_head' and
                     | solve [ auto ] ].

      Lemma fst_redc_loop count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : eval (fst (redc_loop count A_S)) = eval (fst A_S) / r^(Z.of_nat count).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add Hsmall Hbound.
        cbv [redc_loop]; induction_loop count IHcount.
        { simpl; autorewrite with zsimplify; reflexivity. }
        { rewrite IHcount, fst_redc_body by handle_IH_small.
          change (1 + R_numlimbs)%nat with (S R_numlimbs) in *.
          rewrite Zdiv_Zdiv by Z.zero_bounds.
          rewrite <- (Z.pow_1_r r) at 1.
          rewrite <- Z.pow_add_r by lia.
          replace (1 + Z.of_nat count) with (Z.of_nat (S count)) by lia.
          reflexivity. }
      Qed.

      Lemma fst_redc_loop_mod_N count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : eval (fst (redc_loop count A_S)) mod (eval N)
          = (eval (fst A_S) - eval (fst A_S) mod r^Z.of_nat count)
            * ri^(Z.of_nat count) mod (eval N).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds ri_correct.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add Hsmall Hbound ri_correct.
        rewrite fst_redc_loop by assumption.
        destruct count.
        { simpl; autorewrite with zsimplify; reflexivity. }
        { etransitivity;
            [ eapply Z.div_to_inv_modulo;
              try solve [ eassumption
                        | apply Z.lt_gt, Z.pow_pos_nonneg; lia ]
            | ].
          { erewrite <- Z.pow_mul_l, <- Z.pow_1_l.
            { apply Z.pow_mod_Proper; [ eassumption | reflexivity ]. }
            { lia. } }
          reflexivity. }
      Qed.

      Local Arguments Z.pow : simpl never.
      Lemma snd_redc_loop_mod_N count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : (eval (snd (redc_loop count A_S))) mod (eval N)
          = ((eval (snd A_S) + (eval (fst A_S) mod r^(Z.of_nat count))*eval B)*ri^(Z.of_nat count)) mod (eval N).
      Proof using small_N small_B ri_correct lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds k_correct.
        clear -small_N small_B ri_correct r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add k_correct Hsmall Hbound.
        cbv [redc_loop].
        induction_loop count IHcount.
        { simpl; autorewrite with zsimplify; reflexivity. }
        { rewrite IHcount by handle_IH_small.
          push_Zmod; rewrite snd_redc_body_mod_N, fst_redc_body by handle_IH_small; pull_Zmod.
          autorewrite with push_mont_eval; [].
          match goal with
          | [ |- ?x mod ?N = ?y mod ?N ]
            => change (Z.equiv_modulo N x y)
          end.
          destruct A_S as [A S].
          cbn [fst snd].
          change (Z.pos (Pos.of_succ_nat ?n)) with (Z.of_nat (Datatypes.S n)).
          rewrite !Z.mul_add_distr_r.
          rewrite <- !Z.mul_assoc.
          replace (ri * ri^(Z.of_nat count)) with (ri^(Z.of_nat (Datatypes.S count)))
            by (change (Datatypes.S count) with (1 + count)%nat;
                autorewrite with push_Zof_nat; rewrite Z.pow_add_r by lia; simpl Z.succ; rewrite Z.pow_1_r; nia).
          rewrite <- !Z.add_assoc.
          apply Z.add_mod_Proper; [ reflexivity | ].
          unfold Z.equiv_modulo; push_Zmod; rewrite (Z.mul_mod_l (_ mod r) _ (eval N)).
          rewrite Z.mod_pull_div by auto with zarith lia.
          push_Zmod.
          erewrite Z.div_to_inv_modulo;
            [
            | apply Z.lt_gt; lia
            | eassumption ].
          pull_Zmod.
          match goal with
          | [ |- ?x mod ?N = ?y mod ?N ]
            => change (Z.equiv_modulo N x y)
          end.
          repeat first [ rewrite <- !Z.pow_succ_r, <- !Nat2Z.inj_succ by lia
                       | rewrite (Z.mul_comm _ ri)
                       | rewrite (Z.mul_assoc _ ri _)
                       | rewrite (Z.mul_comm _ (ri^_))
                       | rewrite (Z.mul_assoc _ (ri^_) _) ].
          repeat first [ rewrite <- Z.mul_assoc
                       | rewrite <- Z.mul_add_distr_l
                       | rewrite (Z.mul_comm _ (eval B))
                       | rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia;
                         rewrite <- Znumtheory.Zmod_div_mod by (apply Z.divide_factor_r || Z.zero_bounds)
                       | rewrite Zplus_minus
                       | rewrite (Z.mul_comm r (r^_))
                       | reflexivity ]. }
      Qed.

      Lemma pre_redc_bound A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : 0 <= eval (pre_redc A) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds sub_then_maybe_add small_A.
        unfold pre_redc.
        apply redc_loop_good; simpl; autorewrite with push_mont_eval;
          rewrite ?Npos_correct; auto; lia.
      Qed.

      Lemma small_pre_redc A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : small (pre_redc A).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds sub_then_maybe_add small_A.
        unfold pre_redc.
        apply redc_loop_good; simpl; autorewrite with push_mont_eval;
          rewrite ?Npos_correct; auto; lia.
      Qed.

      Lemma pre_redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : (eval (pre_redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds R_numlimbs_nz ri_correct k_correct.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds R_numlimbs_nz ri_correct k_correct sub_then_maybe_add small_A A_bound.
        unfold pre_redc.
        rewrite snd_redc_loop_mod_N; cbn [fst snd];
          autorewrite with push_mont_eval zsimplify;
          [ | rewrite ?Npos_correct; auto; lia.. ].
        Z.rewrite_mod_small.
        reflexivity.
      Qed.

      Lemma redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : (eval (redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
      Proof using small_N small_B ri_correct lgr_big k_correct R_numlimbs_nz N_nz N_lt_R B_bounds.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        autorewrite with push_mont_eval; [].
        break_innermost_match;
          try rewrite Z.add_opp_r, Zminus_mod, Z_mod_same_full;
          autorewrite with zsimplify_fast;
          apply pre_redc_mod_N; auto.
      Qed.

      Lemma redc_bound_tight A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : 0 <= eval (redc A) < eval N + eval B + (if eval N <=? eval (pre_redc A) then -eval N else 0).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds r_big' partition_Proper small_A sub_then_maybe_add.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; lia.
      Qed.

      Lemma redc_bound_N A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : eval B < eval N -> 0 <= eval (redc A) < eval N.
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; lia.
      Qed.

      Lemma redc_bound A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
            (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : 0 <= eval (redc A) < R.
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add A_bound.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; try lia.
      Qed.

      Lemma small_redc A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
            (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : small (redc A).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add A_bound.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        apply small_conditional_sub; [ apply small_pre_redc | .. ]; auto; lia.
      Qed.
    End redc_proofs.

    Section add_sub.
      Context (Av Bv : T R_numlimbs)
              (small_Av : small Av)
              (small_Bv : small Bv)
              (Av_bound : 0 <= eval Av < eval N)
              (Bv_bound : 0 <= eval Bv < eval N).

      Local Ltac do_clear :=
        clear dependent B; clear dependent k; clear dependent ri.

      Lemma small_add : small (add Av Bv).
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        clear -small_Bv small_Av N_lt_R Bv_bound Av_bound partition_Proper r_big' small_N ri k R_numlimbs_nz N_nz B_bounds B sub_then_maybe_add.
        unfold add; t_small.
      Qed.
      Lemma small_sub : small (sub Av Bv).
      Proof using small_N small_Bv small_Av partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R Bv_bound Av_bound. unfold sub; t_small. Qed.
      Lemma small_opp : small (opp Av).
      Proof using small_N small_Bv small_Av partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R Av_bound. unfold opp, sub; t_small. Qed.

      Lemma eval_add : eval (add Av Bv) = eval Av + eval Bv + (if (eval N <=? eval Av + eval Bv) then -eval N else 0).
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        clear -small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound partition_Proper r_big' small_N ri k R_numlimbs_nz N_nz B_bounds B sub_then_maybe_add.
        unfold add; autorewrite with push_mont_eval; reflexivity.
      Qed.
      Lemma eval_sub : eval (sub Av Bv) = eval Av - eval Bv + (if (eval Av - eval Bv <? 0) then eval N else 0).
      Proof using small_Bv small_Av Bv_bound Av_bound small_N partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. unfold sub; autorewrite with push_mont_eval; reflexivity. Qed.
      Lemma eval_opp : eval (opp Av) = (if (eval Av =? 0) then 0 else eval N) - eval Av.
      Proof using small_Av Av_bound small_N partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R.
        clear -Av_bound N_nz small_Av partition_Proper r_big' small_N lgr_big R_numlimbs_nz N_nz N_lt_R.
        unfold opp, sub; autorewrite with push_mont_eval.
        break_innermost_match; Z.ltb_to_lt; lia.
      Qed.

      Local Ltac t_mod_N :=
        repeat first [ progress break_innermost_match
                     | reflexivity
                     | let H := fresh in intro H; rewrite H; clear H
                     | progress autorewrite with zsimplify_const
                     | rewrite Z.add_opp_r
                     | progress (push_Zmod; pull_Zmod) ].

      Lemma eval_add_mod_N : eval (add Av Bv) mod eval N = (eval Av + eval Bv) mod eval N.
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        generalize eval_add; clear. t_mod_N.
      Qed.
      Lemma eval_sub_mod_N : eval (sub Av Bv) mod eval N = (eval Av - eval Bv) mod eval N.
      Proof using small_Bv small_Av Bv_bound Av_bound small_N r_big' partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. generalize eval_sub; clear. t_mod_N. Qed.
      Lemma eval_opp_mod_N : eval (opp Av) mod eval N = (-eval Av) mod eval N.
      Proof using small_Av Av_bound small_N r_big' partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. generalize eval_opp; clear. t_mod_N. Qed.

      Lemma add_bound : 0 <= eval (add Av Bv) < eval N.
      Proof using small_Bv small_Av lgr_big R_numlimbs_nz N_lt_R Bv_bound Av_bound small_N ri k N_nz B_bounds B.
        generalize eval_add; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
      Lemma sub_bound : 0 <= eval (sub Av Bv) < eval N.
      Proof using small_Bv small_Av R_numlimbs_nz Bv_bound Av_bound small_N r_big' partition_Proper lgr_big N_nz N_lt_R.
        generalize eval_sub; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
      Lemma opp_bound : 0 <= eval (opp Av) < eval N.
      Proof using small_Av R_numlimbs_nz Av_bound small_N r_big' partition_Proper lgr_big N_nz N_lt_R.
        clear Bv small_Bv Bv_bound.
        generalize eval_opp; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
    End add_sub.
  End with_args.

  Section modops.
    Context (bitwidth : Z)
            (n : nat)
            (m : Z).
    Let r := 2^bitwidth.
    Local Notation weight := (uweight bitwidth).
    Local Notation eval := (@eval bitwidth n).
    Let m_enc := Partition.partition weight n m.
    Local Coercion Z.of_nat : nat >-> Z.
    Context (r' : Z)
            (m' : Z)
            (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bitwidth_big : 0 < bitwidth)
            (m_big : 1 < m)
            (n_nz : n <> 0%nat)
            (m_small : m < r^n).

    Local Notation wprops := (@uwprops bitwidth bitwidth_big).
    Local Notation small := (@small bitwidth n).

    Local Hint Immediate (wprops) : core.
    Local Hint Immediate (weight_0 wprops) : core.
    Local Hint Immediate (weight_positive wprops) : core.
    Local Hint Immediate (weight_multiples wprops) : core.
    Local Hint Immediate (weight_divides wprops) : core.

    Local Lemma r'_correct_alt : ((r mod m) * (r' mod m)) mod m = 1.
    Proof using r'_correct. pull_Zmod; apply r'_correct. Qed.

    Local Lemma m_enc_correct_montgomery : m = eval m_enc.
    Proof using m_small m_big bitwidth_big.
      clear -m_small m_big bitwidth_big.
      cbv [eval m_enc]; autorewrite with push_eval; auto.
      rewrite uweight_eq_alt by lia.
      Z.rewrite_mod_small; reflexivity.
    Qed.
    Local Lemma r'_pow_correct : (r'^n * r^n) mod (eval m_enc) = 1.
    Proof using r'_correct m_small m_big bitwidth_big.
      clear -r'_correct m_small m_big bitwidth_big.
      rewrite <- Z.pow_mul_l, Z.mod_pow_full, ?(Z.mul_comm r'), <- m_enc_correct_montgomery, r'_correct.
      autorewrite with zsimplify_const; auto with lia.
      Z.rewrite_mod_small; lia.
    Qed.
    Local Lemma small_m_enc : small m_enc.
    Proof using m_small m_big bitwidth_big.
      clear -m_small m_big bitwidth_big.
      cbv [m_enc small eval]; autorewrite with push_eval; auto.
      rewrite uweight_eq_alt by lia.
      Z.rewrite_mod_small; reflexivity.
    Qed.

    Local Ltac t_fin :=
      repeat match goal with
             | _ => assumption
             | [ |- ?x = ?x ] => reflexivity
             | [ |- and _ _ ] => split
             | _ => rewrite <- !m_enc_correct_montgomery
             | _ => rewrite !r'_correct
             | _ => rewrite !Z.mod_1_l by assumption; reflexivity
             | _ => rewrite !(Z.mul_comm m' m)
             | _ => lia
             | _ => exact small_m_enc
             | [ H : small ?x |- context[eval ?x] ]
               => rewrite H; cbv [eval]; rewrite eval_partition by auto
             | [ |- context[weight _] ] => rewrite uweight_eq_alt by auto with lia
             | _=> progress Z.rewrite_mod_small
             | _ => progress Z.zero_bounds
             | [ |- _ mod ?x < ?x ] => apply Z.mod_pos_bound
             end.

    Definition mulmod (a b : list Z) : list Z := @redc bitwidth n m_enc n a b m'.
    Definition squaremod (a : list Z) : list Z := mulmod a a.
    Definition addmod (a b : list Z) : list Z := @add bitwidth n m_enc a b.
    Definition submod (a b : list Z) : list Z := @sub bitwidth n m_enc a b.
    Definition oppmod (a : list Z) : list Z := @opp bitwidth n m_enc a.
    Definition nonzeromod (a : list Z) : Z := @nonzero a.
    Definition to_bytesmod (a : list Z) : list Z := @to_bytesmod bitwidth 1 (2^Z.log2_up m) n a.

    Definition valid (a : list Z) := small a /\ 0 <= eval a < m.

    Lemma mulmod_correct0
      : forall a b : list Z,
        small a -> small b
        -> small (mulmod a b)
          /\ (eval b < m -> 0 <= eval (mulmod a b) < m)
          /\ (eval (mulmod a b) mod m = (eval a * eval b * r'^n) mod m).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros a b Ha Hb. repeat apply conj.
      3: { rewrite !m_enc_correct_montgomery. apply redc_mod_N.  }
      unfold small. unfold mulmod. unfold eval. eapply small_redc; auto. cbv [small mulmod eval];
        [ eapply small_redc
        | rewrite m_enc_correct_montgomery; eapply redc_bound_N
        | rewrite !m_enc_correct_montgomery; eapply redc_mod_N ];
        t_fin.
    Qed.

    Definition onemod : list Z := Partition.partition weight n 1.

    Definition onemod_correct : eval onemod = 1 /\ valid onemod.
    Proof using n_nz m_big bitwidth_big.
      clear -n_nz m_big bitwidth_big.
      cbv [valid small onemod eval]; autorewrite with push_eval; t_fin.
    Qed.

    Lemma eval_onemod : eval onemod = 1.
    Proof. apply onemod_correct. Qed.

    Definition R2mod : list Z := Partition.partition weight n ((r^n * r^n) mod m).

    Definition R2mod_correct : eval R2mod mod m = (r^n*r^n) mod m /\ valid R2mod.
    Proof using n_nz m_small m_big m'_correct bitwidth_big.
      clear -n_nz m_small m_big m'_correct bitwidth_big.
      cbv [valid small R2mod eval]; autorewrite with push_eval; t_fin;
        rewrite !(Z.mod_small (_ mod m)) by (Z.div_mod_to_quot_rem; subst r; lia);
        t_fin.
    Qed.

    Lemma eval_R2mod : eval R2mod mod m = (r^n*r^n) mod m.
    Proof using n_nz m_small m_big m'_correct bitwidth_big. apply R2mod_correct. Qed.

    Definition from_montgomerymod (v : list Z) : list Z
      := mulmod v onemod.

    Lemma from_montgomerymod_correct (v : list Z)
      : valid v -> eval (from_montgomerymod v) mod m = (eval v * r'^n) mod m
                  /\ valid (from_montgomerymod v).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      clear -r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intro Hv; cbv [from_montgomerymod valid] in *; destruct_head'_and.
      replace (eval v * r'^n) with (eval v * eval onemod * r'^n) by (rewrite (proj1 onemod_correct); lia).
      repeat apply conj; apply mulmod_correct0; auto; try apply onemod_correct; rewrite (proj1 onemod_correct); lia.
    Qed.

    Lemma eval_from_montgomerymod (v : list Z) : valid v -> eval (from_montgomerymod v) mod m = (eval v * r'^n) mod m.
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros; apply from_montgomerymod_correct; assumption.
    Qed.
    Lemma valid_from_montgomerymod (v : list Z)
      : valid v -> valid (from_montgomerymod v).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros; apply from_montgomerymod_correct; assumption.
    Qed.

    Lemma mulmod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (mulmod a b)) mod m
                                            = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (mulmod a b)).
    Proof using r'_correct r' n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          try apply mulmod_correct0; cbv [valid] in *; destruct_head'_and; auto; [].
      rewrite !Z.mul_assoc.
      apply Z.mul_mod_Proper; [ | reflexivity ].
      cbv [Z.equiv_modulo]; etransitivity; [ apply mulmod_correct0 | apply f_equal2; lia ]; auto.
    Qed.

    Lemma eval_mulmod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (mulmod a b)) mod m
            = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m).
    Proof. apply mulmod_correct. Qed.

    Lemma squaremod_correct
      : (forall a (_ : valid a), eval (from_montgomerymod (squaremod a)) mod m
                                            = (eval (from_montgomerymod a) * eval (from_montgomerymod a)) mod m)
        /\ (forall a (_ : valid a), valid (squaremod a)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros; cbv [squaremod]; apply mulmod_correct; assumption.
    Qed.

    Lemma eval_squaremod
      : (forall a (_ : valid a),
            eval (from_montgomerymod (squaremod a)) mod m
            = (eval (from_montgomerymod a) * eval (from_montgomerymod a)) mod m).
    Proof. apply squaremod_correct. Qed.

    Local Ltac t_valid_side :=
      repeat first [ solve [ auto ]
                   | apply R2mod_correct
                   | apply mulmod_correct ].

    Definition to_montgomerymod (v : list Z) : list Z
      := mulmod v R2mod.

    Lemma to_montgomerymod_correct
      : (forall v (_ : valid v),
            eval (from_montgomerymod (to_montgomerymod v)) mod m
            = eval v mod m)
        /\ (forall v (_ : valid v), valid (to_montgomerymod v)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros v ?; cbv [to_montgomerymod]; [ | t_valid_side ].
      repeat first [ reflexivity
                   | rewrite !eval_mulmod by t_valid_side
                   | rewrite !eval_from_montgomerymod by t_valid_side
                   | rewrite !eval_R2mod by t_valid_side
                   | rewrite r'_correct_alt
                   | rewrite Z.mul_1_r
                   | rewrite Z.mod_mod by lia
                   | rewrite (Z.mul_comm (r' mod _) (r mod _))
                   | progress push_Zmod
                   | progress (pull_Zmod; rewrite Z.mul_1_r; push_Zmod)
                   | progress (pull_Zmod; rewrite Z.pow_1_l by lia; push_Zmod)
                   | progress (pull_Zmod; rewrite <- !Z.mul_assoc, <- !Z.pow_mul_l; push_Zmod) ].
    Qed.

    Lemma eval_to_montgomerymod
      : forall v (_ : valid v),
        eval (from_montgomerymod (to_montgomerymod v)) mod m
        = eval v mod m.
    Proof. apply to_montgomerymod_correct. Qed.

    Definition encodemod (v : Z) : list Z
      := to_montgomerymod (Partition.partition weight n v).

    Local Ltac t_valid v :=
      cbv [valid]; repeat apply conj;
      auto; cbv [small eval]; autorewrite with push_eval; auto;
      rewrite ?uweight_eq_alt by lia;
      Z.rewrite_mod_small;
      rewrite ?(Z.mod_small (_ mod m)) by (subst r; Z.div_mod_to_quot_rem; lia);
      rewrite ?(Z.mod_small v) by (subst r; Z.div_mod_to_quot_rem; lia);
      try apply Z.mod_pos_bound; subst r; try lia; try reflexivity.
    Lemma encodemod_correct
      : (forall v, 0 <= v < m -> eval (from_montgomerymod (encodemod v)) mod m = v mod m)
        /\ (forall v, 0 <= v < m -> valid (encodemod v)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros v ?; cbv [encodemod];
        [ rewrite eval_to_montgomerymod | apply to_montgomerymod_correct ];
        [ | now t_valid v.. ].
      cbv [eval]; autorewrite with push_eval; auto.
      rewrite ?uweight_eq_alt by lia.
      rewrite ?(Z.mod_small v) by (subst r; Z.div_mod_to_quot_rem; lia).
      reflexivity.
    Qed.

    Lemma eval_encodemod
      : (forall v, 0 <= v < m
                   -> eval (from_montgomerymod (encodemod v)) mod m = v mod m).
    Proof. apply encodemod_correct. Qed.

    Lemma addmod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (addmod a b)) mod m
                                            = (eval (from_montgomerymod a) + eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (addmod a b)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid addmod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_add || eapply add_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with lia; [ ].
      push_Zmod; erewrite eval_add by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with lia); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_addmod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (addmod a b)) mod m
            = (eval (from_montgomerymod a) + eval (from_montgomerymod b)) mod m).
    Proof. apply addmod_correct. Qed.

    Lemma submod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (submod a b)) mod m
                                            = (eval (from_montgomerymod a) - eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (submod a b)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid submod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_sub || eapply sub_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with lia; [ ].
      push_Zmod; erewrite eval_sub by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with lia); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_submod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (submod a b)) mod m
            = (eval (from_montgomerymod a) - eval (from_montgomerymod b)) mod m).
    Proof. apply submod_correct. Qed.

    Lemma oppmod_correct
      : (forall a (_ : valid a), eval (from_montgomerymod (oppmod a)) mod m
                            = (-eval (from_montgomerymod a)) mod m)
        /\ (forall a (_ : valid a), valid (oppmod a)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid oppmod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_opp || eapply opp_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with lia; [ ].
      push_Zmod; erewrite eval_opp by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with lia); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_oppmod
      : (forall a (_ : valid a),
            eval (from_montgomerymod (oppmod a)) mod m
            = (-eval (from_montgomerymod a)) mod m).
    Proof. apply oppmod_correct. Qed.

    Lemma nonzeromod_correct
      : (forall a (_ : valid a), (nonzeromod a = 0) <-> ((eval (from_montgomerymod a)) mod m = 0)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros a Ha; rewrite eval_from_montgomerymod by assumption.
      cbv [nonzeromod valid] in *; destruct_head'_and.
      rewrite eval_nonzero; try eassumption; [ | subst r; apply conj; try eassumption; lia.. ].
      split; intro H'; [ rewrite H'; autorewrite with zsimplify_const; reflexivity | ].
      assert (H'' : ((eval a * r'^n) * r^n) mod m = 0)
        by (revert H'; push_Zmod; intro H'; rewrite H'; autorewrite with zsimplify_const; reflexivity).
      rewrite <- Z.mul_assoc in H''.
      autorewrite with pull_Zpow push_Zmod in H''.
      rewrite (Z.mul_comm r' r), r'_correct in H''.
      autorewrite with zsimplify_const pull_Zmod in H''; [ | lia.. ].
      clear H'.
      generalize dependent (eval a); clear.
      intros z ???.
      assert (z / m = 0) by (Z.div_mod_to_quot_rem; nia).
      Z.div_mod_to_quot_rem; nia.
    Qed.

    Lemma to_bytesmod_correct
      : (forall a (_ : valid a), Positional.eval (uweight 8) (bytes_n (2^Z.log2_up m)) (to_bytesmod a)
                                 = eval a mod m)
        /\ (forall a (_ : valid a), to_bytesmod a = Partition.partition (uweight 8) (bytes_n (2^Z.log2_up m)) (eval a mod m)).
    Proof using m_big n_nz m_small bitwidth_big.
      clear -m_big n_nz m_small bitwidth_big.
      pose proof (Z.log2_up_le_full m).
      generalize (@length_small bitwidth n);
        cbv [valid small to_bytesmod eval]; split; intros; (etransitivity; [ apply eval_to_bytesmod | ]);
          fold weight in *; fold (uweight 8) in *; subst r;
          try solve [ intuition eauto with lia ].
      all: repeat first [ rewrite uweight_eq_alt by lia
                        | lia
                        | reflexivity
                        | progress Z.rewrite_mod_small ].
    Qed.

    Lemma eval_to_bytesmod
      : (forall a (_ : valid a),
            Positional.eval (uweight 8) (bytes_n (2^Z.log2_up m)) (to_bytesmod a)
            = eval a mod m).
    Proof. apply to_bytesmod_correct. Qed.
  End modops.
End WordByWordMontgomery. *)
