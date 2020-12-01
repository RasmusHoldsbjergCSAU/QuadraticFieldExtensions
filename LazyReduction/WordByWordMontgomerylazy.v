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
From Hammer Require Import Tactics.

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
         v.
    Let addT {n} (p q : T n) : T (S n) (* joins carry *)
      := let '(v, c) := Rows.add weight n p q in
         v ++ [c].
    Let drop_high_addT' {n} (p : T (S n)) (q : T n) : T (S n) (* drops carry *)
      := fst (Rows.add weight (S n) p (Positional.extend_to_length n (S n) q)).
    Let conditional_sub {n} (arg : T (S n)) (N : T n) : T n  (* computes [arg - N] if [N <= arg], and drops high bit *)
      := Positional.drop_high_to_length n (Rows.conditional_sub weight (S n) arg (Positional.extend_to_length n (S n) N)).
    Context (R_numlimbs : nat)
            (N : T R_numlimbs). (* encoding of m *)
    Let T_app {n} (p : T n) (e : Z) : T (S n)
        := p ++ [e].
    Let sub_then_maybe_add (a b : T R_numlimbs) : T R_numlimbs (* computes [a - b + if (a - b) <? 0 then N else 0] *)
      := fst (Rows.sub_then_maybe_add weight R_numlimbs (r-1) a b N).
    (* Local Opaque T. *)
    (* Section Iteration.
      Context (pred_A_numlimbs : nat)
              (B : T R_numlimbs) (k : Z)
              (A : T (S pred_A_numlimbs))
              (S : T (S R_numlimbs)).
      (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
      Local Definition A_a := dlet p := @divmod _ A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
      Local Definition S1 := @addT _ S (@scmul _ a B).
      Local Definition s := snd (@divmod _ S1).
      Local Definition q := fst (Z.mul_split r s k).
      Local Definition S2 := @drop_high_addT' _ S1 (@scmul _ q N).
      Local Definition S3' := fst (@divmod _ S2).

      Local Definition A'_S3
        := dlet A_a := @divmod _ A in
           dlet A' := fst A_a in
           dlet a := snd A_a in
           dlet S1 := @addT _ S (@scmul _ a B) in
           dlet s := snd (@divmod _ S1) in
           dlet q := fst (Z.mul_split r s k) in
           dlet S2 := @drop_high_addT' _ S1 (@scmul _ q N) in
           dlet S3 := fst (@divmod _ S2) in
           (A', S3).

      Lemma A'_S3_alt : A'_S3 = (A', S3').
      Proof using Type. cbv [A'_S3 A' S3' Let_In S2 q s S1 A' a A_a]; reflexivity. Qed.
    End Iteration. *)
(* 
    Section loop.
      Context (A_numlimbs : nat)
              (A : T A_numlimbs)
              (B : T R_numlimbs)
              (k : Z)
              (S' : T (S R_numlimbs)).

      Definition redc_body {pred_A_numlimbs} : T (S pred_A_numlimbs) * T (S R_numlimbs)
                                               -> T pred_A_numlimbs * T (S R_numlimbs)
        := fun '(A, S') => A'_S3 _ B k A S'.

      Definition redc_loop (count : nat) : T count * T (S R_numlimbs) -> T O * T (S R_numlimbs)
        := nat_rect
             (fun count => T count * _ -> _)
             (fun A_S => A_S)
             (fun count' redc_loop_count' A_S
              => redc_loop_count' (redc_body A_S))
             count.

      Definition pre_redc : T (S R_numlimbs)
        := snd (redc_loop A_numlimbs (A, @zero (1 + R_numlimbs)%nat)).

      Definition redc : T R_numlimbs
        := conditional_sub pre_redc N.
    End loop. *)

    Section mul_Iteration.
        Context (pred_A_numlimbs : nat)
                (pred_x_numlimbs : nat)
                (B : T R_numlimbs) (k : Z)
                (A : T (S pred_A_numlimbs))
                (x : T pred_x_numlimbs)
                (S : T (S R_numlimbs)).

        Local Definition A_a := dlet p := @divmod _ A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
        Local Definition S1 := @addT _ S (@scmul _ a B).
        Local Definition S2_x1 := (@divmod _ S1).
        Local Definition S2 := fst S2_x1.
        Local Definition x1 := snd S2_x1.
        Local Definition x' := T_app x x1.

        Local Definition A'_x'_S2
        := dlet A_a := @divmod _ A in
            dlet A' := fst A_a in
            dlet a := snd A_a in
            dlet S1 := @addT _ S (@scmul _ a B) in
            dlet S2_x1 := @divmod _ S1 in
            dlet S2 := fst S2_x1 in
            dlet x1 := snd S2_x1 in
            dlet x' := T_app x x1 in
            (A', x', S2).

            Check A'_x'_S2.

        Local Definition A'_x'_S2'
        := dlet A_a := @divmod pred_A_numlimbs A in
            dlet A' := fst A_a in
            dlet a := snd A_a in
            dlet S1 := @addT _ S (@scmul _ a B) in
            dlet S2_x1 := @divmod _ S1 in
            dlet S2 := fst S2_x1 in
            dlet x1 := snd S2_x1 in
            (A', x1, S2).



        Lemma A'_x'_S2_alt : A'_x'_S2 = (A',x', S2).
        Proof using Type. cbv [A'_x'_S2 A' S2 Let_In x1 S2_x1 S1 A' a A_a]; reflexivity. Qed.
    End mul_Iteration.

    Section mul_loop.
        Context (A_numlimbs : nat)
                (A : T A_numlimbs)
                (B : T R_numlimbs)
                (k : Z)
                (S' : T (S R_numlimbs)).

        Definition mul_body {pred_A_numlimbs pred_x_numlimbs} : T (S pred_A_numlimbs) * T pred_x_numlimbs * T (S R_numlimbs)
        -> T pred_A_numlimbs * T (S pred_x_numlimbs) * T (S R_numlimbs)
        := fun '(A, x, S') => A'_x'_S2 pred_A_numlimbs pred_x_numlimbs B A x S'.

         (* Definition mul_loop' (count : nat) : T count * T (S R_numlimbs) -> T O * T (S R_numlimbs) * T count
        := nat_rect
                (fun count => T count * _ -> T O * T (S R_numlimbs) * T count)
                (fun A_S => (A_S, []) )
                (fun count' mul_loop_count' A_S_x
                => let '(Ab, Sb, xb) := (mul_body' (fst (fst A_S_x), snd (fst A_S_x))) in
                    (mul_loop_count' (Ab, Sb), xb)).
                
                mul_loop_count' ((fst (fst mul_body' A_S)), snd (fst mul_body A_S), ))   
                count.  *)
                Check mul_body.
                Check @mul_body.
                Check Nat.pred.
        Definition mul_loop (init : nat) (count : nat) : T (R_numlimbs - init) * T init * T (S R_numlimbs) -> T (R_numlimbs - (init + count)) * T (init + count) * T (S R_numlimbs)
        := nat_rect
                (fun count => T (R_numlimbs - init) * T init * T (S R_numlimbs) -> T (R_numlimbs - (init + count)) * T (init + count) * T (S R_numlimbs))
                (fun A_x_S => A_x_S)
                (fun count' mul_loop_count' A_x_S
                => mul_loop_count' (@mul_body ((R_numlimbs - (init + count))) (init) A_x_S))   
                count.

Check mul_loop.
                (* 
        Definition mul_loop_alt (count : nat) : T count * T (S R_numlimbs) -> T count * T(S R_numlimbs)
        := (fun A_S =>
          let '(A, x, Sr) := mul_loop count ((fst A_S), [], (snd A_S)) in
            (x, Sr)). *)

        Definition pre_mul : T (2 * R_numlimbs + 1)
        := let res := (mul_loop O A_numlimbs (A, [], @zero (1 + R_numlimbs))) in
            snd (fst res) ++ (snd res).

        Definition mul : T (2 * R_numlimbs) := firstn (2 * R_numlimbs) pre_mul.
    End mul_loop.

    Create HintDb word_by_word_montgomery.
    (* Hint Unfold A'_S3 S3' S2 q s S1 a A' A_a Let_In : word_by_word_montgomery. *)

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
            (B_length : length B = R_numlimbs)
            ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
            (k : Z) (k_correct : k * eval N mod r = (-1) mod r).

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


    Lemma length_addT: forall n1 v1 v2, length v1 = n1 -> length v2 = n1 -> length (@addT n1 v1 v2) = S (length v1).
    Proof.
      intros. simpl. unfold addT. destruct (Rows.add weight n1 v1 v2) eqn:eq1. simpl in eq1. rewrite app_length.
      simpl. apply (f_equal (fun y => fst y)) in eq1.
      rewrite Rows.add_partitions in eq1. simpl in eq1. apply (f_equal (fun y : list Z => length y)) in eq1.
      rewrite <- eq1. rewrite Partition.length_partition. all:  auto with zarith.
    Qed.


    Lemma length_sc_mul: forall n v sc, n <> O -> length v = n -> length (@scmul n sc v) = S (length v).
    Proof.
      intros. unfold scmul. destruct (Rows.mul weight r n (S n)) eqn:eq1.
      apply (f_equal (fun y => fst y)) in eq1.
      apply (f_equal (fun (y : list Z) => length y)) in eq1. rewrite Rows.length_mul in eq1. simpl in eq1. rewrite H0.
      all: auto. simpl. rewrite Positional.length_zeros. auto with zarith.
    Qed.

    Lemma undo_div: forall n1 n2: nat, forall A : list Z, length A <> O -> A = snd (@divmod n1 A) :: (fst (@divmod n2 A)).
    Proof. intros. destruct A; [contradiction| auto]. Qed.

    (*These were added*)
    Lemma fst_divmod_nil: forall n n', fst (@divmod n ([] : T n')) = [].
    Proof. auto. Qed.

    Lemma fst_divmod_app: forall n v sc, fst (@divmod n (sc :: v)) = v.
    Proof. auto. Qed.

    Local Opaque T addT drop_high_addT' divmod zero scmul conditional_sub sub_then_maybe_add.
    Create HintDb push_mont_eval discriminated.
    Create HintDb word_by_word_montgomery.
    (* Hint Unfold A'_S3 S3' S2 q s S1 a A' A_a Let_In : word_by_word_montgomery. *)
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

    (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
    (* Section Iteration_proofs.
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
    End redc_proofs. *)
    
    Lemma T_app_small:forall n v sc, small v -> sc_small sc -> small (@T_app n v sc).
    Proof.
      intros. unfold T_app. unfold small. unfold eval. rewrite Positional.eval_snoc with (n := n).
      rewrite Partition.partition_step.
      rewrite Weight.weight_mod_pull_div.
      assert (weight n * sc = sc * weight n). auto with zarith. rewrite H1. rewrite Z_div_plus.
      assert (Positional.eval weight n v / weight n = 0). apply Z.div_small. apply small_bound. auto.
      rewrite H2. simpl.
      rewrite uweight_S. simpl. rewrite Z_div_mult. assert (sc mod 2 ^lgr = sc). apply Z.mod_small. assumption.
      rewrite H3.
      assert ((Partition.partition weight n (Positional.eval weight n v + sc * weight n)) = (Partition.partition weight n (Positional.eval weight n v))).
        - apply partition_eq_mod. auto. apply Z_mod_plus; auto with zarith.
        - rewrite H4. unfold small in H. unfold eval in H. rewrite <- H. auto.
        - auto with zarith.
        - auto with zarith.
        - auto with zarith.
        - auto with zarith.
        - auto with zarith.
        - auto with zarith.
        - symmetry. apply length_small. auto.
        - auto.
    Qed. (*SKRIV DETTE RENT!!*)

    Lemma snd_divmod_sc_small: forall n v, small v -> sc_small (snd (@divmod n v)).
    Proof. intros; unfold sc_small; rewrite eval_mod; auto with zarith. Qed.

    Lemma length_T_app: forall n v sc, length (@T_app n v sc) = S (length v).
    Proof. intros; unfold T_app; rewrite app_length; simpl; auto with zarith. Qed.

    Lemma weight_S: forall i, weight (S i) = r * (weight i).
    Proof. intros. rewrite uweight_S; auto with zarith. Qed.

    Definition eval_hyp sc : list Z -> Prop
    := fun v => (@eval (S (length v)) (sc :: v) = sc + weight 1 * @eval (length v) v).

    Lemma eval_app_aux: forall v sc, @eval (S (length v)) (sc :: v) = sc + (weight 1) * @eval (length v) v.
    Proof.
      intros v sc. generalize dependent v. pose proof (@rev_ind Z (eval_hyp sc)). apply H.
        - unfold eval_hyp. unfold eval. rewrite Positional.eval_nil. unfold Positional.eval, Associational.eval, Positional.to_associational.
          simpl. pose proof wprops. destruct H0. auto with zarith.
        - intros. unfold eval_hyp. unfold eval_hyp in H0. unfold eval. rewrite Positional.eval_snoc with (n := length (l)).
          assert (sc :: l ++ [x] = (sc :: l) ++ [x]). auto. rewrite H1. rewrite Positional.eval_snoc with (n := length (l ++ [x])).
          simpl. unfold eval in H0. assert (length (l ++ [x]) = length (sc :: l)). simpl. rewrite app_length. simpl. auto with zarith.
          simpl in H2. rewrite H2. rewrite H0. simpl.
          Search (_ * (_ + _)). rewrite Z.mul_add_distr_l. Search (_ * (_ * _)). rewrite Z.mul_assoc.
          pose proof wprops. destruct H3. rewrite (weight_S (length l)). unfold r. simpl.
          assert (weight 1 = r). unfold r. unfold weight. simpl. unfold ModOps.weight. simpl. auto. auto with zarith.
          rewrite Z.mul_1_r. Search (_ / 1). rewrite Z.div_1_r. simpl. Search (- (- _)).
          rewrite Z.opp_involutive. auto.
          rewrite H3. unfold r. auto with zarith.
          rewrite app_length. simpl. auto with zarith.
          all: auto.
          rewrite app_length. simpl. auto with zarith.
    Qed.
          

    Definition app_hyp v1 : list Z -> Prop
    := fun v2 => 
        (
          @eval (length v1 + length v2) (v1 ++ v2) = @eval (length v1) v1 + r ^ Z.of_nat (length v1) * @eval (length v2) v2
        ).


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
          all: try rewrite app_length; auto with zarith.
    Qed.

    Local Open Scope Z_scope.

    Lemma eval_T_app: forall v sc, eval (@T_app (length v) v sc) = @eval (length v) (v) + r^(Z.of_nat (length v)) * sc.
    Proof.
      intros. unfold T_app. pose proof eval_app (length v) 1 v [sc]. Local Close Scope Z_scope. assert (S (length v) = length v + 1) by auto with zarith.
      unfold eval. rewrite H0. unfold eval in H. rewrite H.
      assert (Positional.eval weight 1 [sc] = sc).
        - unfold Positional.eval, Positional.to_associational, Associational.eval. simpl.
         rewrite weight_0; [| apply wprops]. auto with zarith.
        - rewrite H1. auto.
        - auto.
        - auto.
    Qed.

Local Open Scope Z_scope.


    Ltac rsmallscmul := apply small_scmul.
    Ltac rsmalladdT := apply small_addT.
(* 
Lemma check_expr: forall {A} (y : A), y = y.
Proof.
reflexivity.
Qed. *)


    Ltac assert_small_op expr := lazymatch expr with
        | scmul ?n1 ?n2 => (rsmallscmul; [assert_small_op n1|auto| auto])
        | addT ?n1 ?n2 => (rsmalladdT; [assert_small_op n1| assert_small_op n2])
        | T_app ?n1 ?n2 => apply T_app_small; [assert_small_op n1| auto]
        | fst (divmod ?n1) => apply small_div; assert_small_op n1
        | _ => auto
    end.
    
    Ltac assert_small := lazymatch goal with
        | |- @small _ ?n1 => assert_small_op n1
        | _ => auto
    end.

    Ltac reduce_eval_expr expr := lazymatch expr with
        | fst (divmod ?n1) => rewrite eval_div; [try apply (f_equal (fun y => y / r)); reduce_eval_expr n1|assert_small]
        | addT ?n1 ?n2 => rewrite eval_addT; [reduce_eval_expr n1; reduce_eval_expr n2| assert_small| assert_small]
        | scmul ?n1 ?n2 => rewrite eval_scmul; [reduce_eval_expr n2| assert_small |auto |auto]
        | snd (divmod ?n1) => rewrite eval_mod; [| |]
        | T_app ?n1 ?n2 => rewrite eval_T_app
        | _ => auto
    end.

    Ltac reduce_eval := lazymatch goal with
        | |- eval ?n1 = _ => reduce_eval_expr n1
        | |- snd (divmod ?n1) = _ => rewrite eval_mod; [try apply (f_equal (fun y => y mod r)); reduce_eval |assert_small]
        | _ => auto
    end.

    Ltac assert_sc_small := try (apply snd_divmod_sc_small); auto.

    (* Ltac reduce_eval' := lazymatch goal with
        | |- eval ?n1 = _ =>
            lazymatch n1 with
              | fst (divmod ?m1) => rewrite eval_div; [try apply (f_equal (fun y => y / r)); reduce_eval'|assert_small]
              | addT ?m1 ?m2 => rewrite eval_addT; [reduce_eval'; reduce_eval'| assert_small| assert_small]
              | scmul ?m1 ?m2 => rewrite eval_scmul; [reduce_eval' | assert_small | assert_sc_small m1 |auto]
              | snd (divmod ?n1) => rewrite eval_mod; [| |]
              | _ => auto
            end
        | |- snd (divmod ?n1 = _) => rewrite eval_mod; [try apply (f_equal (fun y => y mod r)); reduce_eval'| assert_small]
        | _ => auto
    end. *)

    Section mul_iteration_proofs.
        Context (pred_A_numlimbs : nat)
        (A : T (S pred_A_numlimbs))
        (S : T (S R_numlimbs))
        (small_A : small A)
        (small_S : small S).
        (* (S_nonneg : 0 <= eval S). *)

        Local Notation a := (@a pred_A_numlimbs A).
        Local Notation A' := (@A' pred_A_numlimbs A).
        Local Notation S2 := (@S2 pred_A_numlimbs B A S).
        Local Notation x1 := (@x1 pred_A_numlimbs B A S).
        Local Notation x' := (@x' pred_A_numlimbs B A S).

        Local Notation eval_S2 := ((eval S + a * eval B) / r).
        Local Notation eval_x1 := ((eval S + a * eval B) mod r).

        (* Local Coercion eval : T >-> Z. *)

        Lemma a_small: 0 <= a < r.
        Proof. unfold a; rewrite eval_mod; auto with zarith. Qed.

        Lemma eval_S2_eq : eval S2 = eval_S2.
        Proof. pose proof a_small; unfold S2, S2_x1, S1. reduce_eval. Qed.

        Lemma eval_x1_eq : x1 = eval_x1.
        Proof. pose proof a_small; unfold x1, S2_x1, S1; reduce_eval. Qed.

        Lemma S2_x1_invariant : x1 + r * eval S2 = eval S + a * eval B.
        Proof. rewrite eval_S2_eq, eval_x1_eq. rewrite Z_div_mod_eq with (b := r); auto with zarith. Qed.

    End mul_iteration_proofs.

    Section mul_proofs.
      Check pre_mul.
      Check B.
      Local Notation mul_body := (@mul_body B).
      Local Notation mul_loop := (@mul_loop B).
      Local Notation A'_x'_S2 := (@A'_x'_S2 _ _ B).
      Local Notation pre_mul A := (@pre_mul _ A B).

      Section mul_body_proofs.
        Context (pred_A_numlimbs : nat)
                (pred_x_numlimbs : nat)
                (A_x_S : T (S pred_A_numlimbs) * T pred_x_numlimbs * T (S R_numlimbs))
                (A_init : T R_numlimbs).
        Let A := fst (fst A_x_S).
        Let x := snd (fst A_x_S).
        Let Sp := snd (A_x_S).
        Let A_a := divmod A.
        Let A' := fst A_a.
        Let a := snd A_a.
        Context (small_A : small A)
                (small_S : small Sp)
                (small_x: small x)
                (Sp_len: length Sp = (S R_numlimbs))
                (B_len: length B = R_numlimbs)
                (A_len: length A = S (pred_A_numlimbs))
                (x_len: length x = pred_x_numlimbs)
                (A_init_len: length A_init = R_numlimbs)
                (s_len_small: Nat.le pred_x_numlimbs R_numlimbs)
                (A_correct: A = skipn pred_x_numlimbs A_init).
               (* (S_bound : 0 <= eval S < eval N * eval N).*)

        Lemma unfold_A_x_S : A_x_S = (A, x, Sp).
        Proof. destruct A_x_S, p. auto. Qed.

        Lemma unfold_A : A = a :: A'.
        Proof. subst a. simpl. subst A'. subst A_a. rewrite <- (undo_div _ _); auto. rewrite A_len. auto. Qed.  

        Lemma small_fst_fst_mul_body: small (fst (fst (mul_body A_x_S))).
        Proof. destruct A_x_S, p; simpl; assert_small. Qed.

        Lemma small_snd_fst_mul_body: small (snd (fst (mul_body A_x_S))).
        Proof. destruct A_x_S, p; simpl; do 2 (assert_small; assert_sc_small). Qed.

        Lemma small_snd_mul_body: small (snd (mul_body A_x_S)).
        Proof. destruct A_x_S, p; simpl; assert_small; assert_sc_small. Qed.

        Lemma length_A'_x'_S2: length (snd (fst (A'_x'_S2 A x Sp))) = S (length x).
        Proof. simpl; rewrite length_T_app; auto. Qed.

        Lemma length_mul_body_x': length (snd (fst (mul_body A_x_S))) = S (length (snd (fst A_x_S))).
        Proof.
          unfold mul_body. destruct A_x_S, p. simpl. rewrite length_T_app. auto.
        Qed.
        
        Lemma div_nil: forall n, @divmod n [] = ([], 0).
        Proof. reflexivity. Qed.

        Lemma div_app: forall n v a, @divmod n (a :: v) = (v, a).
        Proof. reflexivity. Qed.


        Lemma length_div: forall n v, length (fst (@divmod n v)) = Nat.pred (length v).
        Proof. destruct v; simpl; [rewrite (div_nil n)| rewrite (div_app n v z)]; auto. Qed.


        Lemma length_mul_body_S: length (snd (mul_body A_x_S)) = length (snd A_x_S).
        Proof.
          rewrite unfold_A_x_S. simpl. rewrite length_div. rewrite length_addT; auto.
          rewrite length_sc_mul; auto.
        Qed.

        Lemma mul_body_correct_snd_fst: eval(snd (fst (mul_body A_x_S))) = eval (snd (fst A_x_S)) + ((eval (snd A_x_S) + a * (eval B)) mod r) * r ^ (Z.of_nat pred_x_numlimbs).
        Proof.
          intros. rewrite unfold_A_x_S. simpl. pose proof eval_T_app x ((snd (divmod (addT Sp (scmul (snd (divmod A)) B))))).
          simpl. rewrite <- x_len. rewrite H. rewrite eval_mod. rewrite eval_addT. rewrite eval_scmul.
          simpl. auto with zarith.
          all: assert_small; assert_sc_small.
        Qed.

        Lemma mul_body_correct_snd: eval (snd (mul_body A_x_S)) = (eval Sp + a * eval B) / r.
        Proof.
          rewrite unfold_A_x_S. simpl. reduce_eval. all: assert_sc_small. Qed.

        Lemma exp_succ: forall x n, x ^ (Z.of_nat (S n)) = x ^ (Z.of_nat n) * x.
        Proof. intros; rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r; auto with zarith. Qed.


        Lemma mul_body_correct: length x = pred_x_numlimbs -> eval x + r ^ (Z.of_nat ( pred_x_numlimbs)) * (a * eval B + eval Sp) = (@eval (S pred_x_numlimbs + S R_numlimbs) ((snd ( fst (mul_body A_x_S))) ++ (snd (mul_body A_x_S)))).
        Proof. intros. destruct (mul_body A_x_S) eqn:eq1, p. Local Close Scope Z_scope. assert (S pred_x_numlimbs + S R_numlimbs = S R_numlimbs + S pred_x_numlimbs) by auto with zarith.
        rewrite H0. Local Open Scope Z_scope. unfold Positional.eval. rewrite <- H0.
        rewrite eval_app; simpl.
          - inversion eq1. apply (f_equal (fun y => (snd (fst y)))) in eq1. simpl in eq1.
            assert (length t1 = S (pred_x_numlimbs)). rewrite <- eq1. rewrite length_mul_body_x'. auto.
            rewrite H1. rewrite <- eq1. rewrite mul_body_correct_snd_fst; auto.
            apply (f_equal (fun y => snd y)) in H2. simpl in H2. rewrite <- H2. rewrite mul_body_correct_snd.
            rewrite exp_succ. 
            rewrite (Z.mul_comm (r ^ Z.of_nat pred_x_numlimbs)).  
            rewrite <- (Z.mul_assoc _ r).  rewrite Z.mul_div_eq; [| lia]. rewrite unfold_A_x_S; simpl; auto with zarith.
          - apply (f_equal (fun y => snd (fst y))) in eq1. simpl in eq1. rewrite <- eq1. rewrite length_mul_body_x'. auto.
          - apply (f_equal (fun y => snd y)) in eq1. simpl in eq1. rewrite <- eq1.
            rewrite length_mul_body_S. rewrite unfold_A_x_S. simpl. auto.
        Qed.
        
        Lemma firstn_a: firstn (S pred_x_numlimbs) A = [a] ++ firstn pred_x_numlimbs A'.
        Proof. rewrite unfold_A. auto. Qed.

        Lemma eval_firstn: forall n, @eval (length (firstn ( S n) A)) (firstn (S n) A) = a + r * @eval (length (firstn n A')) (firstn n A').
        Proof. clear x_len.
          intros. rewrite unfold_A. simpl. assert (forall l, a :: l = [a] ++ l) by auto. rewrite H.
          rewrite (eval_app 1 _). simpl. assert (@eval 1 [a] = a). unfold eval, Positional.eval, Positional.to_associational, Associational.eval. simpl. rewrite weight_0; [auto with zarith| apply wprops].
          rewrite H0. all: auto with zarith.
        Qed.

        Lemma eval_sc: forall sc, @eval 1 [sc] = sc.
        Proof. clear x_len.
          intros. unfold eval, Positional.eval, Associational.eval, Positional.to_associational.
          simpl. rewrite weight_0; [auto with zarith | apply wprops].
        Qed. 

        Lemma eval_nil: @eval 0 [] = 0.
        Proof. auto. Qed.

        Lemma skip_pad: forall n (l : list Z), skipn n (Positional.zeros n ++ l) = l.
        Proof. intros. induction n; auto. Qed.

        Local Close Scope Z_scope.
        Lemma skipn_skipn: forall n1 n2 (l : list Z), skipn n1 (skipn n2 l) = skipn (n1 + n2) l.
        Proof.
            intros. generalize dependent l. induction n2.
              - simpl. assert (n1 + 0 = n1) by auto with zarith. rewrite H. auto.
              - intros. rewrite NPeano.Nat.add_succ_r. destruct l.
                + repeat rewrite skipn_nil. auto.
                + simpl. auto.
        Qed.

        Lemma firstn_sum: forall n1 n2 (l : list Z), firstn (n1 + n2) l = firstn n1 l ++ firstn n2 (skipn n1 l).
        Proof.
          induction n1.
            - auto.
            - destruct l eqn:eq1.
              + rewrite skipn_nil. repeat rewrite firstn_nil. auto.
              + simpl. apply (f_equal (fun y => z :: y)). auto.
        Qed.

        Lemma A'_correct: skipn (S pred_x_numlimbs) A_init = A'.
        Proof.
          apply (f_equal (fun (y : list Z) => skipn 1 y)) in A_correct. rewrite unfold_A in A_correct. rewrite skipn_skipn in A_correct.
          simpl in A_correct. rewrite A_correct. auto.
        Qed.

        Lemma firstn_S: forall n (l : list Z) sc l', length l = n -> firstn (S n) (l ++ [sc] ++ l') = l ++ [sc].
        Proof.
          intros. assert (S n = length (l ++ [sc])) by (rewrite app_length; simpl; auto with zarith).
          rewrite H0. assert (length (l ++ [sc]) = length (l ++ [sc]) + 0) by auto. rewrite H1. rewrite app_assoc.
          rewrite firstn_app_2. simpl. rewrite app_nil_r. auto.
        Qed.

        Lemma length_firstn_A_init: length (firstn pred_x_numlimbs A_init) = pred_x_numlimbs.
        Proof. rewrite firstn_length_le; lia. Qed.

        Lemma a_A'_correct: firstn (S pred_x_numlimbs) A_init = firstn (pred_x_numlimbs) A_init ++ [a].
        Proof.
          pose proof (firstn_skipn pred_x_numlimbs A_init). rewrite <- A_correct in H. rewrite unfold_A in H.
          apply (f_equal (fun y => firstn (S pred_x_numlimbs) y)) in H. rewrite <- H.
          assert (forall l (sc : Z) l', l ++ sc :: l' = l ++ [sc] ++ l'). auto.
          rewrite H0. rewrite firstn_S; auto. apply firstn_length_le. lia.
        Qed.
        Local Open Scope Z_scope.

        Lemma mul_body_inv: @eval (pred_x_numlimbs + S (R_numlimbs)) (x ++ Sp) = @eval (length (firstn pred_x_numlimbs A_init)) (firstn pred_x_numlimbs A_init) * eval B ->
            @eval (S pred_x_numlimbs + S (R_numlimbs)) (snd (fst (mul_body A_x_S)) ++ snd (mul_body A_x_S)) = @eval (length (firstn (S pred_x_numlimbs) A_init)) (firstn (S pred_x_numlimbs) A_init) * eval B.
          Proof.
            intros. rewrite a_A'_correct. rewrite <- mul_body_correct; auto. rewrite app_length. rewrite eval_app; auto.
            simpl. rewrite length_firstn_A_init. rewrite eval_sc. rewrite Z.mul_add_distr_r. rewrite length_firstn_A_init in H. rewrite <- H.
            rewrite eval_app; ( try rewrite x_len; auto with zarith).
        Qed.
(* 
        Lemma body_notation : forall n1 n2 (A'' : T (S n1)) (x'' : T n2) S'', (A'_x'_S2 A'' x'' S'') = @mul_body (n1) n2 (A'', x'', S'').
        Proof. reflexivity. Qed.
        Definition eval_loop n (A_x_S' : ( list Z * list Z * list Z)) := @eval (n + S R_numlimbs ) ((eval_loop (fst A_x_S')) ++ (snd A_x_S')). *)
      End mul_body_proofs.

      Check @mul_body.
      Check @A'_x'_S2.
      Lemma body_notation : forall n1 n2 (A : T (S n1)) (x : T n2) Sp, (A'_x'_S2 A x Sp) = @mul_body (S n1) n2 (A, x, Sp).
      Proof. reflexivity. Qed.
      Definition eval_loop n1 n2 (A_x_S' : ( (T (n1)) * T n2 * T (S R_numlimbs))) := @eval (n2 + S R_numlimbs ) ((snd (fst A_x_S')) ++ (snd A_x_S')).

      Check nth.
      Lemma nth_0_divmod: forall n v, nth 0 v 0 = snd (@divmod n v).
      Proof. destruct v; auto. Qed.

      Check T_app.

      Lemma T_app_nil: forall n sc, (@T_app n [] sc) = [sc].
      Proof. reflexivity. Qed.

      Lemma eval_sc': forall sc, @eval 1 [sc] = sc.
      Proof. intros. unfold eval, Positional.eval, Associational.eval, Positional.to_associational. simpl. rewrite weight_0. auto with zarith. apply wprops. Qed. 
      Check @mul_body.
      Check mul_loop.

      Lemma mul_body_snd_fst_length: forall init n1 n2 (x : T( S n1) * T n2 * T (S R_numlimbs)), length (snd (fst x)) = init -> length (snd (fst (@mul_body n1 n2 x))) = S init.
      Proof.
        intros. destruct x, p. simpl. simpl in H. rewrite length_T_app. auto.
      Qed.
      Check mul_body_snd_fst_length.

      Lemma mul_loop_first_it: forall x, mul_loop 0 1 x = mul_body x.
      Proof. reflexivity. Qed.

      Check nat_rect.
      Check mul_loop.
      Check @mul_loop.
      Lemma mul_loop_next_inner: forall n n' x, mul_loop n' (S n) x = mul_loop (S n') n (mul_body x).
      Proof. auto. Qed.

        Lemma mul_loop_body_comm: forall n n' x, mul_body (mul_loop n' n x) = mul_loop (S n') n (mul_body x).
       Proof.
        intros. generalize dependent n'. induction n.
          - auto.
          - intros. pose proof (mul_loop_next_inner n). rewrite (H n'). remember (mul_body x) as x'.
            remember (IHn (S n') x'). repeat rewrite <- Nat.add_succ_comm.
            rewrite e. rewrite (H (S n') ). auto.
       Qed.
        Lemma mul_loop_next: forall n x, mul_body (mul_loop 0 n x) = mul_loop 0 (S n) x.
       Proof. intros.
       
        induction n as [|n' IHn'].
          - reflexivity.
          - simpl. pose proof (mul_loop_next_inner (S n') 0 x).  pose proof (mul_loop_body_comm (S n') 0 x). Set Printing All. repeat rewrite <- Nat.add_succ_comm.
            repeat rewrite <- Nat.add_succ_comm in H. rewrite H. auto.
       Qed.

       Local Close Scope Z_scope.
       Lemma mul_loop_snd_fst_length: forall n init (x : T (R_numlimbs - init) * (T init) * T(S R_numlimbs)), length (snd (fst x)) = init -> length (snd( fst (mul_loop init n x))) = init + n.
       Proof. Local Open Scope Z_scope.
         induction n.
          - intros. unfold mul_loop. simpl. rewrite Nat.add_0_r. auto with zarith.
          - intros. repeat rewrite <- Nat.add_succ_comm. pose proof (mul_loop_next_inner n init x). repeat rewrite <- Nat.add_succ_comm in H0. Set Printing All. rewrite H0.
            rewrite IHn. auto. apply mul_body_snd_fst_length. auto.
       Qed.


       Lemma nth_fst_fst_mul_body: forall n1 n2 n x, nth n (fst (fst (@mul_body n1 n2 x))) 0 = nth (S n) (fst (fst x)) 0.
       Proof.
         intros. destruct x, p. simpl. destruct t0 eqn:eq1.
          - rewrite (fst_divmod_nil n1); auto with zarith. Search (nth). repeat rewrite nth_overflow; simpl; auto with zarith.
          - simpl. rewrite (fst_divmod_app n1). auto.
       Qed.
    
       
       Lemma divmod_fst_fst_mul_loop: forall n1 n2 n x, (snd (@divmod n1 (fst (fst( mul_loop n2 n x))))) = nth n (fst (fst x)) 0.
       Proof. intros. generalize dependent n2.
         induction n.
          - intros. rewrite nth_0_divmod with (n := n1). auto.
          - intros. repeat rewrite Nat.add_succ_comm. pose proof (mul_loop_next_inner n n2 x). rewrite H.
            pose proof (IHn (S n2) (mul_body x)).
            Set Printing All. repeat rewrite Nat.add_succ_comm. repeat rewrite Nat.add_succ_comm in H0.
            rewrite H0. rewrite nth_fst_fst_mul_body. auto.
       Qed.
 

       Lemma nat_sub: forall x y, (S x <= y)%nat -> S (y - S x) = (y - x)%nat.
       Proof.
          intros. rewrite <- Nat.sub_succ_l. rewrite NPeano.Nat.sub_succ; auto. auto. Qed.

        Lemma nat_sub_0: forall y : nat, (y - 0)%nat = y.
        Proof. auto with zarith. Qed.

        Lemma nat_0_add_r: forall y, (0 + y)%nat = y.
        Proof. auto. Qed.

        Lemma length_mul_body_snd: forall n1 n2 x, length (snd x) = S R_numlimbs -> length (snd (@mul_body n1 n2 x)) = S R_numlimbs.
        Proof.
          intros. destruct x, p. simpl.
          rewrite length_div. rewrite length_addT. all: auto.
          rewrite length_sc_mul; auto.
        Qed.

        Lemma length_mul_loop_snd: forall x count, length (snd x) = S R_numlimbs -> length (snd (mul_loop 0 count x)) = S R_numlimbs.
        Proof.
          intros. generalize dependent x. induction count.
          - intros. unfold mul_loop. simpl. auto.
          - intros. rewrite <- mul_loop_next.
            rewrite (length_mul_body_snd _ _ (mul_loop 0 count x)); auto.
        Qed.


        Lemma length_fst_fst_mul_body: forall x n n1 n2, length (fst (fst x)) = n -> length (fst (fst (@mul_body n1 n2 x))) = (n - 1)%nat.
        Proof.
          intros. destruct x, p. simpl. rewrite length_div.
          Search Nat.pred. rewrite pred_of_minus. simpl in H. auto.
        Qed. 
          
        Lemma length_fst_fst_mul_loop_inv: forall count x, length (fst (fst x)) = R_numlimbs
        -> length (fst (fst (mul_loop 0 count x))) = (R_numlimbs - count)%nat
        -> length (fst (fst (mul_loop 0 (S count) x))) = (R_numlimbs - (S count))%nat.
        Proof.
          intros. rewrite <- mul_loop_next. rewrite (length_fst_fst_mul_body (mul_loop 0 count x) (R_numlimbs - count) _ _).
          auto with zarith. auto.
        Qed.

         Lemma length_fst_fst_mul_loop: forall count x, length (fst (fst x)) = R_numlimbs 
          -> length (fst (fst (mul_loop 0 count x))) = (R_numlimbs - count)%nat.
        Proof.
          intros. generalize dependent x. induction count.
            - intros. unfold mul_loop. simpl. assert (forall y : nat, (y - 0)%nat = y). auto with zarith.
              rewrite H0. auto.
            - intros. rewrite length_fst_fst_mul_loop_inv; auto.
        Qed. 

        Lemma length_snd_fst_mul_body: forall n1 n2 x, length (snd (fst (@mul_body n1 n2 x))) = S (length (snd (fst x))).
        Proof.
          intros. destruct x, p. simpl. rewrite length_T_app. auto.
        Qed.

        Lemma length_snd_fst_mul_loop: forall count x, (snd (fst x)) = ([] : T 0) -> length (snd (fst ( mul_loop 0 count x))) = (count)%nat.
        Proof.
          intros. generalize dependent x. induction count.
          - intros. unfold mul_loop. simpl. Set Printing All. rewrite H. auto.
          - intros. rewrite <- mul_loop_next. rewrite (length_snd_fst_mul_body _ _ (mul_loop 0 count x)).
            auto.
        Qed.

        Lemma fst_fst_mul_body_skipn: forall n1 n2 x, (fst (fst (@mul_body n1 n2 x))) = (skipn 1 (fst (fst x))).
        Proof.
          intros. destruct x, p. simpl. reflexivity.
        Qed.

        Lemma fst_fst_mul_loop_skipn: forall count x, fst (fst (mul_loop 0 count x)) = skipn count (fst (fst x)).
        Proof.
          intros. generalize dependent x. induction count.
            - intros. unfold mul_loop. simpl. auto.
            - intros. rewrite <- mul_loop_next. rewrite (fst_fst_mul_body_skipn _ _).
              rewrite IHcount. rewrite skipn_skipn. auto.
        Qed.

        (* Lemma small_fst_fst_mul_loop_inv: forall count x, (S count <= R_numlimbs)%nat
          -> small (fst (fst (mul_loop 0 count x)))
          -> small (fst (fst (mul_loop 0 (S count) x))).
        Proof.
          intros. rewrite <- mul_loop_next. apply small_fst_fst_mul_body with (A_init := fst( fst( x))).
            + repeat rewrite nat_0_add_r. repeat rewrite nat_0_add_r in H0.
              repeat rewrite nat_sub; auto.
            + rewrite small_snd

        Lemma small_fst_fst_mul_loop_inv: forall count x, (S count <= R_numlimbs)%nat -> small (fst (fst x)) -> small (fst (fst (mul_loop 0 count x))).
        Proof.
          intros. generalize dependent x. induction count.
            - intros. unfold mul_loop. simpl. auto.
            - intros. rewrite <- mul_loop_next. apply small_fst_fst_mul_body with (A_init := fst (fst x)).
              + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount. *)

        Lemma small_mul_loop: forall count x, (S count <= R_numlimbs)%nat
          -> small (fst (fst x))
          -> (snd (fst x)) = []
          -> length (snd x) = (S R_numlimbs)
          -> length (fst (fst x)) = R_numlimbs
          -> small (snd (fst (mul_loop 0 count x)))
          -> small (fst (fst (mul_loop 0 count x)))
          -> small (snd (mul_loop 0 count x))
          -> small (fst (fst (mul_loop 0 (S count) x))) /\
              small (snd (fst (mul_loop 0 (S count) x))) /\
              small (snd (mul_loop 0 (S count) x)).
       Proof.
         intros. repeat split.
          - rewrite <- mul_loop_next. pose proof (small_fst_fst_mul_body (R_numlimbs - (S count)) count (mul_loop 0 count x) (fst (fst x))).
            apply H7; auto.
            + Set Printing All. repeat rewrite nat_sub. apply H5. auto.
            + pose proof (length_mul_loop_snd x count). apply H8. auto.
            + pose proof (length_fst_fst_mul_loop count x). repeat rewrite nat_0_add_r in H6.
              Set Printing All. repeat rewrite nat_sub; auto.
            + pose proof (length_snd_fst_mul_loop count x). Set Printing All.
              repeat rewrite nat_sub. repeat rewrite nat_0_add_r in H8. rewrite H8; auto. auto.
            + pose proof (fst_fst_mul_loop_skipn count x). repeat rewrite nat_0_add_r in H8. repeat rewrite nat_sub; auto.
          - rewrite <- mul_loop_next. pose proof (small_snd_fst_mul_body (R_numlimbs - (S count)) count (mul_loop 0 count x) (fst (fst x))).
            apply H7. repeat rewrite nat_0_add_r in H5. repeat rewrite nat_sub; auto. auto.
            repeat rewrite nat_0_r in H4. repeat rewrite nat_sub; auto.
            pose proof (length_mul_loop_snd x count). apply H8. auto.
            repeat rewrite nat_sub; auto.
            pose proof (length_fst_fst_mul_loop count x). repeat rewrite nat_0_add_r in H8. auto.
            pose proof (length_snd_fst_mul_loop count x). repeat rewrite nat_sub; auto.
            apply (fst_fst_mul_loop_skipn count x).
          - rewrite <- mul_loop_next. apply small_snd_mul_body with (A_init := fst(fst x)).
            + repeat rewrite nat_0_add_r. repeat rewrite nat_0_add_r in H5.
              repeat rewrite nat_sub; auto.
            + auto.
            + auto.
            + pose proof (length_mul_loop_snd x count). apply H7. auto.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop. auto.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply length_snd_fst_mul_loop. auto.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply fst_fst_mul_loop_skipn.
       Qed.

       Lemma small_fst_fst_mul_loop: forall count x, (S count <= R_numlimbs)%nat
       -> small (fst (fst x))
       -> (snd (fst x)) = []
       -> length (snd x) = (S R_numlimbs)
       -> length (fst (fst x)) = R_numlimbs
       -> small (snd (fst (mul_loop 0 count x)))
       -> small (fst (fst (mul_loop 0 count x)))
       -> small (snd (mul_loop 0 count x))
       -> small (fst (fst (mul_loop 0 (S count) x))).
       Proof. apply small_mul_loop. Qed.

        Lemma small_snd_fst_mul_loop: forall count x, (S count <= R_numlimbs)%nat
          -> small (fst (fst x))
          -> (snd (fst x)) = []
          -> length (snd x) = (S R_numlimbs)
          -> length (fst (fst x)) = R_numlimbs
          -> small (snd (fst (mul_loop 0 count x)))
          -> small (fst (fst (mul_loop 0 count x)))
          -> small (snd (mul_loop 0 count x))
          -> small (snd (fst (mul_loop 0 (S count) x))).
        Proof. apply small_mul_loop. Qed.
            

        Lemma small_snd_mul_loop: forall count x, (S count <= R_numlimbs)%nat
          -> small (fst (fst x))
          -> (snd (fst x)) = []
          -> length (snd x) = (S R_numlimbs)
          -> length (fst (fst x)) = R_numlimbs
          -> small (snd (fst (mul_loop 0 count x)))
          -> small (fst (fst (mul_loop 0 count x)))
          -> small (snd (mul_loop 0 count x))
          -> small (snd (mul_loop 0 (S count) x)).
        Proof. apply small_mul_loop. Qed.

        Lemma small_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (fst (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))) /\
           small (snd (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))) /\
           small (snd (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs)))).
        Proof. induction count.
            - intros. unfold mul_loop. simpl. repeat split; auto.
            - intros. repeat split.
              + rewrite <- mul_loop_next. apply small_fst_fst_mul_body with (A_init := A).
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply (IHcount A); auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply (IHcount A); auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply (IHcount A); auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. pose proof (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs))). apply H1.
                  simpl. rewrite repeat_length. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
                  simpl. auto. Search small. rewrite length_small. rewrite nat_sub_0. auto. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                  apply length_snd_fst_mul_loop. simpl. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply fst_fst_mul_loop_skipn.
              + rewrite <- mul_loop_next. apply small_snd_fst_mul_body with (A_init := A).
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. pose proof (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs))). apply H1.
                  simpl. rewrite repeat_length. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
                  simpl. auto. Search small. rewrite length_small. rewrite nat_sub_0. auto. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                  apply length_snd_fst_mul_loop. simpl. auto.
                * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply fst_fst_mul_loop_skipn.
              + rewrite <- mul_loop_next. apply small_snd_mul_body with (A_init := A).
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply IHcount; auto; lia.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. pose proof (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs))). apply H1.
                simpl. rewrite repeat_length. auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
                simpl. auto. Search small. rewrite length_small. rewrite nat_sub_0. auto. auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                apply length_snd_fst_mul_loop. simpl. auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply fst_fst_mul_loop_skipn.
        Qed.

        Lemma small_fst_fst_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (fst (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))).
        Proof. apply small_mul_loop'. Qed.

        Lemma small_snd_fst_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (snd (fst (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))))).
        Proof. apply small_mul_loop'. Qed.

        Lemma small_snd_mul_loop': forall count A, small A -> (count <= R_numlimbs)%nat
        -> small (snd (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs)))).
        Proof. apply small_mul_loop'. Qed.


      Lemma mul_loop_inv (A: T (R_numlimbs)): forall count,
      small A ->
      (S (S count) <= R_numlimbs)%nat 
      -> eval_loop (R_numlimbs - count) count (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))) + r ^ (Z.of_nat count) *  (nth count A 0) * eval B = eval_loop (R_numlimbs - (S count)) (S count) (mul_loop O (S count) (A, [], Positional.zeros (S R_numlimbs)))
      -> eval_loop (R_numlimbs - (S count)) (S count) (mul_loop 0 (S count) (A, [], Positional.zeros (S R_numlimbs))) + r ^ (Z.of_nat (S count)) *  (nth (S count) A 0) * eval B = eval_loop (R_numlimbs - (S (S count))) (S (S count)) (mul_loop O (S (S count)) (A, [], Positional.zeros (S R_numlimbs))).
      Proof. intros c' H Hcount H'. assert (A_len: length A = R_numlimbs) by (rewrite length_small; auto). 
      - unfold eval_loop. rewrite <- (mul_loop_next (S c')).
        remember (A, [], Positional.zeros (S R_numlimbs)) as x.
        unfold eval_loop in H'. 
        repeat rewrite eval_app. rewrite eval_app in H'. rewrite eval_app in H'.
        rewrite mul_body_correct_snd with (A_init := A).
        rewrite mul_body_correct_snd_fst with (A_init := A).
        rewrite mul_body_snd_fst_length with (init := (S c')).
        assert (forall y, r ^ Z.of_nat (S y) = r * r ^ Z.of_nat y). Search (_ ^ (_ + _)).
        Local Close Scope Z_scope.
        assert (S (S c') = 1 + S c') as H'' by auto with zarith. intros. Local Open Scope Z_scope. assert (Z.of_nat(S y) = 1 + Z.of_nat y). auto with zarith. rewrite H0. rewrite Zpower_exp. auto with zarith. lia. lia. 
        rewrite H0. rewrite H0. 
        rewrite <- Z.mul_assoc. rewrite <- Z.mul_assoc. rewrite <- Z.mul_assoc. rewrite (Z.mul_comm (r ^ Z.of_nat (S c'))).
        rewrite Z.mul_assoc. assert (Z.of_nat (0 + S c') = Z.of_nat (S c')). auto with zarith.
        rewrite H1. Check Z.mul_add_distr_r. repeat rewrite <- Z.add_assoc. rewrite Z.mul_assoc. rewrite Z.mul_assoc. rewrite <- (Z.mul_add_distr_r _ _ (r ^ Z.of_nat (S c'))).
        rewrite <- Z.div_mod'' with (b := r). rewrite (mul_loop_snd_fst_length (S c') 0) in H'.
        rewrite H1 in H'. rewrite Z.mul_add_distr_r. rewrite (Z.mul_comm _ (r ^ Z.of_nat (S c'))).
        rewrite Z.add_assoc. rewrite Z.add_assoc. simpl in Heqx.
        Set Printing All. assert (forall y, Init.Nat.add O y = y) by auto with zarith. repeat rewrite H2.
        Set Printing All. Local Close Scope Z_scope. assert (forall y, ((S y) <= R_numlimbs) -> S (Init.Nat.sub R_numlimbs (S y)) = Init.Nat.sub R_numlimbs y).
        intros. rewrite <- NPeano.Nat.sub_succ_l. 
         rewrite Nat.sub_succ. auto. auto.
         rewrite H3. rewrite <- H'.
         rewrite <- mul_loop_next. rewrite mul_body_correct_snd_fst with (A_init := A).
         rewrite mul_body_correct_snd with (A_init := A). rewrite H2.
         rewrite mul_body_snd_fst_length with (init := c'). rewrite H0.
         rewrite (mul_loop_snd_fst_length c' 0). repeat rewrite H2. rewrite <- Z.mul_assoc.
         rewrite (Z.mul_comm (r ^ (_)) _). rewrite Z.mul_assoc. repeat rewrite H3.
         Local Open Scope Z_scope.
         assert (forall y1 y2 y3 y4, y1 + y2 + y3 + y4 = y1 + (y2 + y3) + y4). auto with zarith.
         rewrite H4. 
         rewrite <- (Z.mul_add_distr_r _ _ (Z.pow r (Z.of_nat c'))).
         rewrite <- Z.div_mod''. simpl.
         repeat rewrite <- Z.add_assoc.
         apply (f_equal (fun y => eval (snd (fst (mul_loop 0 c' x))) + y)).
         rewrite Z.mul_add_distr_r. rewrite Z.mul_comm.
         repeat rewrite <- Z.add_assoc.
         apply (f_equal (fun y => r ^ Z.of_nat c' * eval (snd (mul_loop 0 c' x)) + y)).
         simpl. pose proof divmod_fst_fst_mul_loop.
         rewrite (H5 _ O c').
         rewrite (mul_loop_next c'). rewrite (H5 _ O (S c')).
         simpl. auto with zarith. rewrite Heqx. simpl. auto with zarith.
         all: auto with zarith; try lia; try (rewrite Heqx; auto; assert_small).
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto; try lia.
            apply length_snd_fst_mul_loop. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto; try lia.
            apply small_fst_fst_mul_loop'; auto; try lia. rewrite nat_sub_0. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_mul_loop'.
              * rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_fst_mul_loop'.  
              * rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. 
            apply (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs)) c').
            simpl. rewrite repeat_length. auto.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_fst_fst_mul_loop). simpl. auto.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_snd_fst_mul_loop). simpl. auto.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (small_fst_fst_mul_loop'). rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (small_snd_mul_loop'). rewrite nat_sub_0. auto.
              * lia.
              * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (small_snd_fst_mul_loop'). rewrite nat_sub_0. auto.
            * lia. 
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_mul_loop_snd). simpl. rewrite repeat_length; auto.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_fst_fst_mul_loop. simpl. auto.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. simpl. auto.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
            * lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply (length_snd_fst_mul_loop). auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_fst_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_mul_loop.
              * lia.
              * simpl. rewrite nat_sub_0. auto.
              * auto.
              * simpl. rewrite repeat_length. auto.
              * auto.
              * repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
                apply small_snd_fst_mul_loop'. rewrite nat_sub_0. auto.
                lia.
              * apply small_fst_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
              * apply small_snd_mul_loop'. rewrite nat_sub_0. auto. lia.
          + apply small_snd_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_mul_loop_snd. simpl. rewrite repeat_length; auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_fst_fst_mul_loop. simpl. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. simpl. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_fst_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply small_snd_mul_loop'. rewrite nat_sub_0. auto. lia.
          + apply small_snd_fst_mul_loop'. rewrite nat_sub_0. auto. lia.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_mul_loop_snd.
            simpl. rewrite repeat_length; auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_fst_fst_mul_loop.
            simpl. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. auto.
          + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply fst_fst_mul_loop_skipn.
          + apply length_snd_fst_mul_loop. auto.
          + apply length_mul_loop_snd. simpl. rewrite repeat_length. auto.
          + apply length_snd_fst_mul_loop. auto.
          + apply length_mul_loop_snd. simpl. rewrite repeat_length. auto.
          + rewrite length_snd_fst_mul_body. apply (f_equal (fun y => S y)).
            repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
            apply length_snd_fst_mul_loop. auto.
          + rewrite length_mul_body_snd; auto.
          repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. apply length_mul_loop_snd.
          simpl. rewrite repeat_length. auto.
          + apply length_snd_fst_mul_loop. auto.
          + apply length_mul_loop_snd. simpl. rewrite repeat_length; auto.
      Qed.
        

      Lemma mul_loop_eval (A: T (R_numlimbs)): forall count,
      small A ->
      (S count <= R_numlimbs)%nat
      -> eval_loop (R_numlimbs - count) count (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))) + r ^ (Z.of_nat count) *  (nth count A 0) * eval B = eval_loop (R_numlimbs - (S count)) (S count) (mul_loop O (S count) (A, [], Positional.zeros (S R_numlimbs))).
      Proof. intros. assert (Alen: length A = R_numlimbs) by (apply length_small; auto). induction count.
        - pose proof (mul_body_correct (R_numlimbs - 1) 0 (A, [], (Positional.zeros (S R_numlimbs))) A). unfold mul_body in H1. unfold eval_loop. simpl in H1.
          assert (Init.Nat.sub R_numlimbs O = R_numlimbs). auto with zarith. simpl. rewrite <- H1; try auto. rewrite eval_zero. simpl.
          rewrite (@nth_0_divmod (Init.Nat.sub R_numlimbs (S O)) A). rewrite Z.add_0_r. destruct (snd (divmod A)) eqn:eq1; auto with zarith.
          destruct (p * eval B); auto. destruct (Z.neg p * eval B); auto.
          + rewrite nat_sub; auto. rewrite nat_sub_0. auto.
          + reflexivity.
          + rewrite repeat_length; auto.
          + auto with zarith.
          + auto with zarith.
        - apply mul_loop_inv; auto. apply IHcount. lia.
      Qed.


      Definition first_n n : T R_numlimbs -> T n
      := fun (A : T R_numlimbs) => (firstn n A).

      Lemma first_n_length: forall n A, (n <= length A)%nat -> length (first_n n A) = n.
      Proof.
        intros. rewrite firstn_length. lia.
      Qed.

      Lemma first_n_S: forall n n1 (A : T (n1)), (n < length A)%nat -> first_n (S n) A = (first_n n A) ++ [nth n A 0].
      Proof.
        intros. rewrite firstn_succ with (d := 0). rewrite nth_default_eq. auto. auto.
      Qed.

      Lemma eval_first_n_S : forall n n1 (A : T n1), (n < length A)%nat -> eval (first_n (S n) A) = eval (first_n n A) + r ^ Z.of_nat n * (nth n A 0).
      Proof.
        intros.
        assert ((first_n (S n) A) = (first_n n A) ++ [nth n A 0]). apply first_n_S. auto.
        rewrite H0. pose proof (eval_app n 1 (first_n n A) [nth n A 0]). simpl in H1.
        Set Printing All. rewrite Nat.add_1_r in H1. rewrite H1. rewrite eval_sc'.
        rewrite first_n_length. all: (auto; try lia). apply first_n_length. lia.
      Qed.

      
      Lemma mul_loop_eval_first (A: T(R_numlimbs)) n: small A -> (n <= R_numlimbs)%nat -> eval_loop (R_numlimbs - n) n (mul_loop 0 n (A, [], Positional.zeros (S R_numlimbs)))
        = (eval (first_n n A) * eval B).
      Proof. intros. induction n.
        - unfold mul_loop, eval_loop, eval. simpl. rewrite Positional.eval_zeros. auto.
        - rewrite <- mul_loop_eval. rewrite IHn. rewrite eval_first_n_S. auto with zarith.
          all: (auto with zarith; try lia). rewrite length_small; auto.
      Qed. 

      Lemma mul_loop_eval_full (A: T (R_numlimbs)): small A ->
      eval_loop 0 R_numlimbs (mul_loop 0 R_numlimbs (A, [], Positional.zeros (S R_numlimbs)))
        = eval (A) * eval B.
        Proof. intros.
            pose proof (mul_loop_eval_first A R_numlimbs). Search Init.Nat.sub. rewrite NPeano.Nat.sub_diag in H0. rewrite H0.
            auto. pose proof length_small H. rewrite <- H1. unfold first_n. rewrite List.firstn_all. auto.
            auto. auto.
        Qed.

      Lemma mul_loop_step (A : T (R_numlimbs)): small A -> forall count, eval_loop (R_numlimbs - count) count (mul_loop 0 count (A, [], Positional.zeros (S R_numlimbs))) + r ^ (Z.of_nat count) *  (nth count A 0) * eval B = eval_loop (R_numlimbs - (S count)) (S count) (mul_loop O (S count) (A, [], Positional.zeros (S R_numlimbs))).
      Proof. intros. assert (A_len: length A = R_numlimbs) by (rewrite length_small; auto). induction count as [| c' IHc'].
        - pose proof (mul_body_correct (R_numlimbs - 1) 0 (A, [], (Positional.zeros (S R_numlimbs))) A).
          simpl. unfold mul_body in H0. unfold eval_loop. simpl. simpl in H0.
          Set Printing All. assert (Init.Nat.sub R_numlimbs O = R_numlimbs). auto with zarith.
          Set Printing All. rewrite <- H0; try auto. rewrite eval_zero. simpl.
          rewrite (@nth_0_divmod (Init.Nat.sub R_numlimbs (S O)) A). rewrite Z.add_0_r. destruct (snd (divmod A) * eval B); auto.
          all: admit.
        - unfold eval_loop. rewrite <- (mul_loop_next (S c')).
          remember (A, [], Positional.zeros (S R_numlimbs)) as x.
          unfold eval_loop in IHc'.
          repeat rewrite eval_app. rewrite eval_app in IHc'. rewrite eval_app in IHc'.
          rewrite mul_body_correct_snd with (A_init := A).
          rewrite mul_body_correct_snd_fst with (A_init := A).
          rewrite mul_body_snd_fst_length with (init := (S c')).
          assert (forall y, r ^ Z.of_nat (S y) = r * r ^ Z.of_nat y). Search (_ ^ (_ + _)).
          Local Close Scope Z_scope.
          assert (S (S c') = 1 + S c') as H' by auto with zarith. intros. Local Open Scope Z_scope. assert (Z.of_nat(S y) = 1 + Z.of_nat y). auto with zarith. rewrite H0. rewrite Zpower_exp. auto with zarith. lia. lia. 
          rewrite H0. rewrite H0. 
          rewrite <- Z.mul_assoc. rewrite <- Z.mul_assoc. rewrite <- Z.mul_assoc. rewrite (Z.mul_comm (r ^ Z.of_nat (S c'))).
          rewrite Z.mul_assoc. assert (Z.of_nat (0 + S c') = Z.of_nat (S c')). auto with zarith.
          rewrite H1. Check Z.mul_add_distr_r. repeat rewrite <- Z.add_assoc. rewrite Z.mul_assoc. rewrite Z.mul_assoc. rewrite <- (Z.mul_add_distr_r _ _ (r ^ Z.of_nat (S c'))).
          rewrite <- Z.div_mod'' with (b := r). rewrite (mul_loop_snd_fst_length (S c') 0) in IHc'.
          rewrite H1 in IHc'. rewrite Z.mul_add_distr_r. rewrite (Z.mul_comm _ (r ^ Z.of_nat (S c'))).
          rewrite Z.add_assoc. rewrite Z.add_assoc. simpl in Heqx.
          Set Printing All. assert (forall y, Init.Nat.add O y = y) by auto with zarith. repeat rewrite H2.
          Set Printing All. Local Close Scope Z_scope. assert (forall y, ((S y) <= R_numlimbs) -> S (Init.Nat.sub R_numlimbs (S y)) = Init.Nat.sub R_numlimbs y).
          intros. rewrite <- NPeano.Nat.sub_succ_l. 
           rewrite Nat.sub_succ. auto. auto.
           rewrite H3. rewrite <- IHc'.
           rewrite <- mul_loop_next. rewrite mul_body_correct_snd_fst with (A_init := A).
           rewrite mul_body_correct_snd with (A_init := A). rewrite H2.
           rewrite mul_body_snd_fst_length with (init := c'). rewrite H0.
           rewrite (mul_loop_snd_fst_length c' 0). repeat rewrite H2. rewrite <- Z.mul_assoc.
           rewrite (Z.mul_comm (r ^ (_)) _). rewrite Z.mul_assoc. repeat rewrite H3.
           Local Open Scope Z_scope.
           assert (forall y1 y2 y3 y4, y1 + y2 + y3 + y4 = y1 + (y2 + y3) + y4). auto with zarith.
           rewrite H4. 
           rewrite <- (Z.mul_add_distr_r _ _ (Z.pow r (Z.of_nat c'))).
           rewrite <- Z.div_mod''. simpl.
           repeat rewrite <- Z.add_assoc.
           apply (f_equal (fun y => eval (snd (fst (mul_loop 0 c' x))) + y)).
           rewrite Z.mul_add_distr_r. rewrite Z.mul_comm.
           repeat rewrite <- Z.add_assoc.
           apply (f_equal (fun y => r ^ Z.of_nat c' * eval (snd (mul_loop 0 c' x)) + y)).
           simpl. pose proof divmod_fst_fst_mul_loop.
           rewrite (H5 _ O c').
           rewrite (mul_loop_next c'). rewrite (H5 _ O (S c')).
           simpl. auto with zarith. rewrite Heqx. simpl. auto with zarith.
           all: auto with zarith; try lia; try (rewrite Heqx; auto; assert_small).
            + admit.
            + simpl. pose proof mul_loop_snd_fst_length c' 0 x. rewrite Heqx in H4.
              assert (forall y, (0 + y)%nat = y). auto. repeat rewrite H5 in H4.
              Set Printing All. repeat rewrite nat_sub. rewrite H4. auto.
              * auto.
              * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply small_fst_fst_mul_loop'; auto.
              repeat rewrite nat_sub_0. auto.
              * admit.
              * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply small_snd_mul_loop'.
                * rewrite nat_sub_0. auto.
                * admit.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply small_snd_fst_mul_loop'.  
                * rewrite nat_sub_0. auto.
                * admit.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto. 
              apply (length_mul_loop_snd (A, [], Positional.zeros (S R_numlimbs)) c').
              simpl. rewrite repeat_length. auto.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply (length_fst_fst_mul_loop). simpl. auto.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply (length_snd_fst_mul_loop). simpl. auto.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply fst_fst_mul_loop_skipn.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply (small_fst_fst_mul_loop'). rewrite nat_sub_0. auto.
                * admit.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply (small_snd_mul_loop'). rewrite nat_sub_0. auto.
                * admit.
                * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply (small_snd_fst_mul_loop'). rewrite nat_sub_0. auto.
              * admit. 
              * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply (length_mul_loop_snd). simpl. rewrite repeat_length; auto.
              * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply length_fst_fst_mul_loop. simpl. auto.
              * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply length_snd_fst_mul_loop. simpl. auto.
              * admit.
            + repeat rewrite nat_0_add_r. repeat rewrite nat_sub; auto.
              apply fst_fst_mul_loop_skipn.
              * admit.
            + admit.
            +

            pose proof (small_fst_fst_mul_loop ).
              apply small_mul_loop. destruct H4.
            Set Printing All. rewrite small_fst_fst_mul_body.
              
          pose proof (mul_body_inv). unfold mul_loop. unfold eval_loop in IHc'. 
          
          rewrite <- H0. simpl in H0.
          Set Printing All.
          rewrite <- H0.
          rewrite eval_app. rewrite eval_app. simpl. rewrite eval_zero. simpl. unfold eval. Local Close Scope Z_scope. assert (1%nat = 0%nat + 1%nat). auto. rewrite H0.
          pose proof eval_T_app. repeat rewrite <- nth_0_divmod. simpl. unfold T_app. simpl.
          Check eval_sc. (rewrite eval_sc'). simpl. rewrite T_app_nil.
            destruct A eqn:eq1. simpl in H. rewrite <- H in R_numlimbs_nz. contradiction.
             simpl. Local Open Scope Z_scope.


          destruct A. simpl in H. rewrite <- H in R_numlimbs_nz. contradiction.
           simpl in H.  rewrite <- H. rewrite body_notation.
        rewrite body_notation. unfold eval. simpl. simpl. rewrite body_notation. unfold eval_loop. pose proof (mul_body_correct (R_numlimbs - 1) 0 (A, [], (Positional.zeros (S R_numlimbs))) A).
          rewrite eval_app; auto. rewrite eval_app; auto.
          rewrite eval_app in H0. simpl. simpl. simpl in H0.
          Set Printing All.
          rewrite <- H0.  Set Printing All. simpl. Set Printing All. simpl in H0.
          Set Printing All.
          rewrite <- H0.
          unfold eval. unfold eval in H0. Set Printing All. rewrite H0.
          rewrite H0.
        
        
        pose proof (mul_body_correct R_numlimbs 0 (A, ([] : list Z), Positional.zeros (S R_numlimbs)) A).
          destruct A eqn:eq1.
            + simpl. simpl in H. rewrite <- H in R_numlimbs_nz. contradiction.
            + simpl in H. simpl. rewrite <- H. unfold eval_loop. Set Printing All. rewrite body_notation.
          rewrite body_notation.

        Set Printing All.
          unfold eval_loop.  
          simpl. simpl in H. rewrite <- H; (auto with zarith; try lia).
          Set Printing All. 
          rewrite body_notation.
        simpl.
          Set Printing All.
          rewrite body_notation.
          
          rewrite <- H.
        
      
      
      
      intros count. pose proof (mul_body_correct O (S count) (A, ([] : list Z), Positional.zeros (S R_numlimbs)) A). induction count as [|c' IHc'].
        - simpl. Set Printing All. rewrite body_notation. unfold eval_loop. Set Printing All.
      
      simpl. rewrite body_notation. rewrite <- H. Set Printing All.
        induction count.
          - Set Printing All. simpl. Set Printing All. rewrite body_notation. unfold eval_loop.  
           pose proof (mul_body_correct O (S O) (A, ([] : list Z), Positional.zeros (S R_numlimbs)) A). Set Printing All.
           unfold mul_body in H. Set Printing All. unfold mul_body. unfold eval. unfold eval in H. Set Printing All. rewrite <- H.
           assert (Positional.eval weight (1 + S R_numlimbs)
           (snd (fst (A'_x'_S2 A ([] : list Z) (Positional.zeros (S R_numlimbs)))) ++
            snd (A'_x'_S2 A ([] : list Z) (Positional.zeros (S R_numlimbs)))) 
            = (Positional.eval weight 0
            (snd (fst (A, ([] : list Z), Positional.zeros (S R_numlimbs)))) +
          r ^ Z.of_nat 0 *
          (snd (@divmod pred_A_numlimbs (fst (fst (A, ([] : list Z), Positional.zeros (S R_numlimbs))))) *
           Positional.eval weight R_numlimbs B +
           Positional.eval weight (S R_numlimbs)
             (snd (A, ([] : list Z), Positional.zeros (S R_numlimbs)))))
           ).
           
           unfold divmod.
            unfold eval in H. unfold mul_body in H. unfold mul_body. rewrite eval_app in H. rewrite eval_app. rewrite eval_app.
            unfold eval. unfold eval in H. unfold divmod in H. rewrite <- H.

            rewrite <- H.
          unfold eval in H.
            
            
            destruct A. simpl.
        destruct (mul_loop O count A_x_S) as [p S'] eqn:eq1. destruct p as [A' x'] eqn:eq2.
        induction count.
          - admit.
          -
        

      Check T_app.
       (* Lemma mul_app: forall A x x' S, mul_loop count (A, (T_app x x'), S) =
        (fst (fst (mul_loop count (A, x, S))),
         T_app 
        )  *)


      Local Close Scope Z_scope.
      Lemma mul_loop_good init count A_x_S 
          (Hsmall: small (snd(fst A_x_S)) /\ small (fst (fst A_x_S)) /\ small (snd A_x_S)) :
          small (snd (fst (mul_loop init count A_x_S))) /\ small (fst (fst (mul_loop init count A_x_S))) /\ small (snd (mul_loop init count A_x_S)).
        Proof. generalize dependent init. induction count as [|count' IHcount'].
          - intros init A_x_S Hsmall. auto. simpl. auto. unfold small. unfold small in Hsmall. destruct Hsmall, H0. repeat split. 2: auto.
            2: auto.
            unfold eval. unfold eval in H. destruct init. simpl. auto.
             simpl. assert (forall n : nat, n + 0 = n). auto with zarith. remember (H2 init) as Hinit. rewrite Hinit. auto.
          - intros. simpl. assert (init + S count' = S init + count') by auto with zarith.
            rewrite H.
            apply (IHcount' (S init)). destruct Hsmall, H1.
            repeat split.
              + apply small_snd_fst_mul_body in H0; auto.
              + apply small_fst_fst_mul_body in H1; auto.
              + apply small_snd_mul_body in H2; auto.
        Qed. (*Skriv dette rent!!!*)

      Local Open Scope Z_scope.
      Lemma pre_mul_correct: forall A, eval (@pre_mul A) = (@eval R_numlimbs (A)) * (eval B).
      Proof.
        intros. unfold pre_mul. unfold mul_loop. unfold mul_body. unfold A'_x'_S2. simpl.

          
          
          
          simpl.
          
          destruct init.
            + simpl. auto. intros. simpl.
          
          
          
          simpl. intros. Check (mul_body A_x_S). Check (IHcount' (S init) (mul_body A_x_S)).
            remember (IHcount' (S init) (mul_body A_x_S)) as thisH. unfold small.
            unfold small in thisH. assert (forall n m, n + S m = S n + m) by auto with zarith. rewrite H. apply thisH.
            simpl. auto. unfold small in Hsmall. destruct Hsmall, H1. repeat split.

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

End WordByWordMontgomery.
