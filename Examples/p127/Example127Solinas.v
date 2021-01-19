Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import ZArith Znumtheory List.
Require Import Crypto.Arithmetic.Saturated.
Require Import Coqprime.Z.Pmod.
Require Import Lia.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Stringification.IR.
Require Import Theory.QuadraticFieldExtensions.
Require Import Coqprime.elliptic.GZnZ.

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.C.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.BoundsPipeline.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.PushButtonSynthesis.SaturatedSolinas.

Import
Language.Compilers
Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional.
Import ListNotations.
Import Util.LetIn.
Import ZUtil.Definitions.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.

(** ======= these are the changable parameters ====== *)
Definition s := 2^127.
Definition c := [(1, 1)].
Let machine_wordsize := 64.
Definition p := Eval compute in (s - Associational.eval c).
(** ================================================= *)
Let possible_values := [0; 1; 64; 128].
Definition n := 2%nat.
Hypothesis n_val: n = Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
Let m := s - Associational.eval c.
Let nreductions : nat :=
  let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
  Z.to_nat (Qceiling (Z.of_nat n / (Z.of_nat n - i))).
Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
Let boundsn : list (ZRange.type.option.interp base.type.Z)
  := repeat bound n.
Definition w := weight 64 1.


Require Import Crypto.Util.ListUtil.

Lemma combine_lemma: forall (A: Type) x' l x n, S (length l) = n -> @combine Z A (map w (seq 0 (n + 1))) (x' :: l ++ [x]) = combine (map w (seq 0 n)) (x' :: l) ++ [(w n, x)].
Proof.
    intros A x' l x n Hl. assert (H: seq 0 (n + 1) = (seq 0 n ++ [n])).
        - assert (n + 1 = S n) by auto with zarith. assert (seq 0 (n + 1) = seq 0 (S n)). auto with zarith. rewrite H0. rewrite seq_S. simpl. auto.
        - rewrite H. rewrite map_app. simpl. remember (map w (seq 0 n)) as l1. remember (x' :: l) as l2.
          assert (x' :: l ++ [x] = (x' :: l) ++ [x]). auto. rewrite H0. rewrite combine_snoc. rewrite Heql2. auto.
          simpl. rewrite Heql1. assert (length (seq 0 n) = n). simpl. apply seq_length. rewrite map_length. rewrite H1. auto.
Qed.



Lemma mulmod_rep_compat: forall l x n, length l = n -> Positional.eval w (n + 1) (l ++ [x])
    = (Positional.eval w n l) +  (w n) * x.
Proof.
    intros l x n H. induction l as [|x' l' IHl'].
        - simpl. simpl in H. rewrite <- H. simpl. unfold eval. unfold to_associational. simpl. unfold Associational.eval. simpl. auto with zarith.
        - unfold eval. unfold to_associational. simpl. rewrite combine_lemma.
          rewrite eval_app. assert (Associational.eval [(w n, x)] = w n * x). unfold Associational.eval. simpl. auto with zarith.
          rewrite H0. auto.
          simpl in H. auto.
Qed.
(*viser at list Z * Z -> list Z korrekt for Rows.mulmod*)

Instance subrelation_eq_impl : subrelation eq Basics.impl.
congruence.
Qed.

Instance subrelation_eq_flip_impl : subrelation eq (Basics.flip Basics.impl).
congruence.
Qed.

Definition mulp := @Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c 2 nreductions.

Lemma list_len_neq_0: forall (A : Type) (l : list A), 0 < length l -> exists l' x, l = l' ++ [x].
Proof.
    intros A l H. induction l as [|x l' IHl'].
        - simpl in H. discriminate H.
        - destruct l' eqn:eq.
            + exists [], x. auto.
            + assert (0 < length (a :: l)). auto. apply IHl' in H0. inversion H0. inversion H1.
              exists  (x :: x0). exists x1. rewrite H2. auto.
Qed.

Definition all_ge_0 l := forall x, In x l -> 0 <= x.



Lemma weight_ge_0: forall m, 0 <= (w m).
Proof.
    intros; unfold w, weight; auto with zarith.
Qed.

Definition list_prop l := forall m, all_ge_0 l -> length l = m -> 0 <= Positional.eval w m l.

Lemma mulmod_fst_ge_0: forall x, all_ge_0 x -> list_prop x.
intros. apply (rev_ind list_prop).
    - unfold list_prop. intros. rewrite eval_nil. auto with zarith.
    - intros z x' H2 m H3 H4. unfold list_prop. rewrite last_length in H4. rewrite <- H4.
      rewrite eval_snoc_S; [|reflexivity]. unfold list_prop in H2. apply Z.add_nonneg_nonneg.
       + apply H2. intros p H'. assert (In p (x' ++ [z])) by (apply in_or_app; auto). apply H3 in H0. auto.
         auto.
       + assert (In z (x' ++ [z])) by (apply in_or_app; right; simpl; auto). apply H3 in H0.
         apply Ztac.mul_le; [apply weight_ge_0 |auto].
Qed.
(*
Lemma mulmod_all_ge_0: forall x y, all_ge_0 x -> all_ge_0 y -> all_ge_0 (fst (mulp x y)).
Proof.
    intros. remember (fst (mulp x y)) as l. induction l.
        - unfold all_ge_0; contradiction.
        - unfold mulp in Heql. unfold Rows.mulmod in Heql. Check Rows.flatten. unfold Rows.flatten in Heql.
          unfold Rows.flatten' in Heql.
Qed.







Lemma mulmod_snd_0: forall x y, (snd (Saturated.Rows.mulmod w 64 s c n nreductions x y)) mod (s - Associational.eval c) = 0.
Proof.
    intros x y. destruct (snd (Rows.mulmod w 64 s c n nreductions x y) mod (s - Associational.eval c) =? 0) eqn:eq.
        - rewrite Z.eqb_eq in eq; auto.
        - rewrite Z.eqb_neq in eq. remember (snd (Rows.mulmod w 64 s c n nreductions x y) mod (s - Associational.eval c)) as t.
          assert (0%Z <= t).
          rewrite Heqt.
          remember (snd (Rows.mulmod w 64 s c n nreductions x y)) as t'. remember (s - Associational.eval c) as p.
          assert (H: 0 <= t' mod p < p).
            + Check t'. Check p. Check Z.mod_pos_bound.
            apply Z.mod_pos_bound. rewrite Heqp. simpl. auto. auto with zarith.
            + destruct H. auto.
            + assert (H': 0 < t). apply Z.le_neq. auto.                
              assert (forall m, 1 <= m -> t * m >= m). intros m Hm. apply Z.ge_le_iff.
              rewrite Z.mul_comm. apply Z.le_mul_diag_r. 1, 2: lia.
              assert ((Positional.eval w n (fst (mulp x y))
              + w n * (snd (mulp x y))) mod (s - Associational.eval c)
              = (Positional.eval w n x * Positional.eval w n y) mod (s - Associational.eval c)). apply Saturated.Rows.eval_mulmod.
              apply wprops. lia. unfold machine_wordsize. lia. unfold s; lia. unfold s, c; simpl; auto with zarith.
              unfold n. auto. 1, 2: admit. Search Positional.eval.



          lia. auto with zarith.
          assert (H: forall x, Positional.eval w n x <= p).
            + intros. Search Positional.eval. induction x0.
                * rewrite Positional.eval_nil. unfold p. auto with zarith.
                * rewrite eval_cons.


*)

Definition mulp_sat_gen := @Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c 2 nreductions.
Definition mulp_sat := @Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c 2 nreductions.
Definition evalp x := Positional.eval w n x.

Lemma mul_general : mulp_sat_gen = mulp_sat.
Proof. auto. Qed.


(*
Lemma testlem : forall x y n, n <> 0%nat -> length x = n -> length y = n
    -> (Positional.eval w n (fst (mulp_sat_gen x y)) + (w n) * (snd (mulp_sat_gen x y))) mod (s - Associational.eval c)
        = (((Positional.eval w n x) * (Positional.eval w n y) mod (s - Associational.eval c))).
Proof.
    intros. unfold mulp_sat_gen. rewrite Saturated.Rows.eval_mulmod. try (unfold s; auto with zarith). 2: unfold machine_wordsize; auto with zarith.
    2: unfold c; simpl; auto with zarith.
    About weight_properties. apply wprops. unfold machine_wordsize; auto with zarith.
Qed.

Definition mulp x y := let (p, p') := mulp_sat x y in
    p ++ [p'] .
Definition evalp x := Positional.eval w n x.

Lemma mulp_format: forall x y, mulp x y = (fst (mulp_sat x y)) ++ [snd (mulp_sat x y)].
Proof. auto. Qed.
*)

Definition subp x y := Saturated.Rows.sub w n x y.

Definition n1 := 3.
Definition n2 := 7.
Definition enc x := Positional.encode w 2 s c x.
Definition s1 := enc n1.
Definition s2 := enc n2.


(* 
Lemma mulp_correct: forall x y, (evalp x * evalp y) mod p = evalp (mulp x y) mod p.
Proof.
    intros. rewrite mulp_format. unfold evalp. pose proof Saturated.Rows.eval_mulmod. unfold evalp. rewrite <- mul_general. induction n as [|n' IHn'].
        - rewrite 2!eval0; auto with zarith.
        - assert (S n' = (n' + 1)%nat). auto with zarith. rewrite H0. rewrite Positional.eval_snoc with (n := n'); auto. rewrite mulmod_rep_compat. *)


(* 
Check Saturated.Rows.mulmod.
Check Saturated.Rows.flatten'.
Check ModOps.carry_mulmod.

About Positional.



Check Positional.encode w 2 s c.

Definition thatx := 2^63 + 1.
Definition thaty := 2^64.


Definition encx x := Positional.encode w 2 s c x.
Definition thisx := encx thatx.
Definition thisy := encx thaty.

Eval compute in thisx.
Eval compute in thisy.

Eval compute in (mulp_sat thisx thisy).


Eval compute in (w 2).
Eval compute in (2^128).

Check flat_map.
Check Columns.eval.

Lemma test: forall x y, snd (mulp_sat x y) = 0.
Proof.
    intros. unfold mulp_sat. Check Rows.mulmod. unfold Rows.mulmod. Check Rows.flatten. unfold Rows.flatten.
    Check Rows.flatten'. unfold Rows.flatten'. Check fold_right. Search fold_right. remember x as thisx. induction (length x) as [|l' IHl'] eqn:eq.
    - Search ((length _) = 0).
Qed.

Local Existing Instances ToString.C.OutputCAPI Pipeline.show_ErrorMessage.
Local Instance : only_signed_opt := false.
Local Instance : no_select_opt := false.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : use_mul_for_cmovznz_opt := false.
Local Instance : emit_primitives_opt := true.
Local Instance : should_split_mul_opt := false.
Local Instance : should_split_multiret_opt := false.
Local Instance : widen_carry_opt := false.
Local Instance : widen_bytes_opt := true. (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)
Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.
Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.
Local Existing Instance ToString.C.OutputCAPI.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : emit_primitives_opt := true.
  
Time Redirect "log" Compute
      Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
      false
     (Pipeline.BoundsPipelineToString
        "fiat" "mul"
        false (* subst01 *)
        None (* fancy *)
        possible_values
        machine_wordsize
        ltac:( let n := (eval cbv in n) (* needs to be reduced to reify correctly *) in
        let nreductions := (eval cbv in nreductions) (* needs to be reduced to reify correctly *) in
        let r := Reify (@Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c n nreductions) in
        exact r)
               (fun _ _ => []) (* comment *)
               (Some boundsn, (Some boundsn, tt))
               (Some boundsn, Some r[0~>0x1]%zrange (* Should be: Some r[0~>0]%zrange, but bounds analysis is not good enough *) )).





(*See https://github.com/mit-plv/fiat-crypto/blob/3f58bfab8d6cb098f0a75d3738e03e939478356c/src/SlowPrimeSynthesisExamples.v#L100-L304
søg efter "not exactly equal to a weight, we must adjust it t"*)

Require Import Crypto.SlowPrimeSynthesisExamples.




Definition nred := Eval compute in (nreductions machine_wordsize c n). 
Hypothesis p_prime: prime p.
Hypothesis p_ge2: 2 < p.
Hypothesis pmod: p mod 4 =? 3 = true.
Definition w := ModOps.weight 64 1.
Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).
Check QuadraticFieldExtensions.Quad_non_res.
Lemma quad_res_minus_1: Quad_non_res p = ((-1) zmod p).
Proof.
    reflexivity.
Qed.

Check Rows.mulmod.


Eval compute in (Rows.adjust_s w 6 s).
Eval compute in (2^128).



About Saturated.Rows.mulmod.
Check Positional.encode.
Definition mul127 x y := (Saturated.Rows.mulmod w base s c 2 nred x y).
Definition eval127' z := (Positional.eval w 2 z).
Definition enc127 z := Positional.encode w 2 s c z.

Check mul127.






Local Notation "x *p y" := (mul127 x y) (at level 90).

Require Import Crypto.Util.LetIn.
Check @ModOps.addmod.

Definition add127 x y : list Z := ModOps.addmod.


Eval compute in ModOps.weight 64 1 2.
Eval compute in (2^128).

Definition mulFp2 := fun x y => let '(x1, x2) := x in
    let '(y1, y2) := y in
    dlet v0 := (x1) *p (y1) in
        dlet v1 := (x2) *p (y2) in
            (
                v0 -p v1,
                ((((x1) +p (x2)) *p ((y1) +p (y2))) -p v0) -p v1
            ).

Definition  mulFp2r x1 x2 y1 y2 :=
        dlet v0 := (x1) *p (y1) in 
        dlet v1 := (x2) *p (y2) in
            (
                v0 -p v1,
                dlet f1 := x1 +p x2 in
                    dlet f2 := y1 +p y2 in
                        dlet v2 := f1 *p f2 in
                            dlet v3 := v2 -p v0 in
                                v3 -p v1
            ).


Definition mulFp2reif (x11 x12 x21 x22 y11 y12 y21 y22 : Z) := let '(z1, z2) := (mulFp2 ([x11; x12], [x21; x22]) ([y11; y12], [y21; y22])) in
    [nth_default 0 z1 0; nth_default 1 z1 0; nth_default 0 z2 0; nth_default 1 z2 0].
(*
Definition mulFp2r (x1 x2 y1 y2 : list Z) := mulFp2 (x1, x2) (y1, y2).
*)
Definition hej (l1 l2 l3 l4: list Z) : list Z :=
    l1 +p l2 +p l3.

Definition hej2 x1 x2 y1 y2 :=
    (dlet v0 := (x1 +p y1) in (
            dlet v1 := (x2 +p y2) in (
                x1,
                x2
            )
        )
    ).

Definition to_montgomeryFp2 x := (tomont127 (val p (fst x)), tomont127 (val p (snd x))).


Definition eval_Fp2 x :=
    (
        eval127(fst x) zmod p,
        eval127(snd x) zmod p
    ).

(*testing*)

Definition z1 := (543254938987987935443 zmod p, 5433 zmod p).
Definition z2 := (65433 zmod p, 2457 zmod p).
Definition mon1 := to_montgomeryFp2 z1.
Definition mon2 := to_montgomeryFp2 z2.
Definition eval1 := eval_Fp2 mon1.
Definition eval2 := eval_Fp2 mon2.

Definition prod := mulFp2r (fst mon1) (snd mon1) (fst mon2) (snd mon2).
Definition prodeval := eval_Fp2 prod.


(*Eval compute in (elem1).*)
Eval compute in (mon1).
Eval compute in (mon2).

Eval compute in prod.
Eval compute in prodeval.
Definition x1 := [2303232; 9223605965625171200].
Definition x2 := [18446325046823417597; 9223138782394246399].
Eval compute in eval_Fp2 (x1, x2).

Eval compute in (2^64).

Eval compute in 18446465859655129087.

Definition out0 := .



Time Redirect "log" Compute
     (Pipeline.BoundsPipelineToString
        "fiat_" "fial_mulFp2_"
        false None [64; 128] 64
        ltac:(let r := Reify (mulFp2r) in
              exact r)
              (fun _ _ => [])
              (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt))))%zrange
              (Some (repeat (Some r[0~>2^64 - 1]) 2), Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange).





Lemma eval_correct: forall x, x = ((eval127 (tomont127 (val p x))) zmod p).
Proof.
    intros x. case x. simpl. intros val inZnZ. apply zirr. unfold eval127, tomont127. Check WordByWordMontgomery.eval_encodemod.
    rewrite WordByWordMontgomery.eval_encodemod with (r' := 2 ^63); try auto; unfold p, c, s; simpl; unfold Z.pow_pos; simpl; try lia.
    rewrite inZnZ. unfold p, c, s; simpl. apply Z_mod_lt. lia.
Qed.


Lemma eval_compat: forall x n, Positional.eval w n x = @WordByWordMontgomery.eval 64 n x.
Proof. auto. Qed.

Lemma eval_encode: forall x n, n <> 0%nat -> Positional.eval w n (Positional.encode w n s c x) mod p = x mod p.
Proof.
    intros. apply Positional.eval_encode; (unfold s, c, p; auto with zarith; try lia).
    - intros. unfold w, uweight. assert (0 < weight 64 1 i). apply weight_positive, wprops; lia. lia.
    - simpl; lia.
    - intros. unfold w, uweight. assert (0 < (weight 64 1 (S i)) / (weight 64 1 i)). apply weight_divides, wprops; lia. lia.
Qed.


Eval compute in (uweight 64 1).

Theorem eval_tomont_inv: forall val, 0 <= val < p -> eval127 (tomont127 val) mod p = val.
Proof.
    intros val H; unfold eval127, tomont127; rewrite WordByWordMontgomery.eval_encodemod with (r' := 2 ^ 63);
    (unfold p, s, c; simpl; unfold Z.pow_pos; simpl; auto with zarith; lia).
Qed.


Theorem to_montFp2_correct: forall x y, eval_Fp2 (to_montgomeryFp2 (x, y)) = (x, y).
Proof.
    intros; unfold eval_Fp2; apply injective_projections; [case x | case y];
    intros val Hval; apply zirr; simpl; apply eval_tomont_inv;
    rewrite Hval; apply Z_mod_lt; unfold p, c, s; simpl; lia.
Qed.

Definition tomontFp2:= fun x => (tomont127 (val p (fst x)), tomont127 (val p (snd x))).
Definition evalFp2:= fun x => (eval127 (fst x) zmod p, eval127 (snd x) zmod p).

Local Ltac thisauto := unfold p, c, s; simpl; unfold Z.pow_pos; simpl; auto with zarith.

(*SKRIV DETTE RENT!!!!!*)
Theorem add127_correct: forall x y, (eval127(tomont127 (val p x) +p tomont127 (val p y)) zmod p) = add p x y.
Proof.
    intros x y. unfold add127. unfold add. simpl. apply zirr. unfold eval127.
    rewrite WordByWordMontgomery.eval_addmod with (r' := 2 ^ 63); [|thisauto|thisauto|thisauto|thisauto|thisauto|thisauto| | ].
        - unfold tomont127. rewrite PullPush.Z.add_mod_full.
        assert  (forall z, (@WordByWordMontgomery.eval 64 2
                (WordByWordMontgomery.from_montgomerymod 64 2 p 1
                (WordByWordMontgomery.encodemod 64 2 p 1 z)) mod p)
           = eval127 (tomont127 z) mod p); [auto|].
        do 2 rewrite H.
        repeat rewrite eval_tomont_inv; try reflexivity;
        [destruct y| destruct x]; simpl; rewrite inZnZ; apply Z_mod_lt; thisauto.
        - pose proof WordByWordMontgomery.encodemod_correct 64 2 p (2 ^ 63) 1. apply H;
          try ( unfold p, c, s; simpl; unfold Z.pow_pos; simpl; auto with zarith; lia).
          destruct x. simpl. rewrite inZnZ. apply Z_mod_lt. unfold p, c, s; simpl; lia.
        - unfold tomont127.
          pose proof WordByWordMontgomery.encodemod_correct 64 2 p (2 ^ 63) 1. apply H;
          try ( unfold p, c, s; simpl; unfold Z.pow_pos; simpl; auto with zarith; lia).
          destruct y. simpl. rewrite inZnZ. apply Z_mod_lt. unfold p, c, s; simpl; lia.
Qed.

Theorem add_correct: forall x y, evalFp2 (addFp2 (tomontFp2 x) (tomontFp2 y)) = addp2 p x y.
Proof.
    intros x y. unfold evalFp2, tomontFp2. simpl. unfold addp2. apply injective_projections; (simpl; rewrite add127_correct; reflexivity).
Qed.


Theorem mul127_correct: forall x y, (eval127 (tomont127 (val p x) *p tomont127 (val p y)) zmod p) = mul p x y.
Proof.
    intros x y. unfold mul127. unfold mul. simpl. apply zirr. unfold eval127.
    rewrite WordByWordMontgomery.eval_mulmod with (r' := 2 ^ 63); [|thisauto|thisauto|thisauto|thisauto|thisauto|thisauto| | ].
        - unfold tomont127. rewrite Z.mul_mod; [| unfold p, c, s; simpl; auto with zarith].
        assert  (forall z, (@WordByWordMontgomery.eval 64 2
                (WordByWordMontgomery.from_montgomerymod 64 2 p 1
                (WordByWordMontgomery.encodemod 64 2 p 1 z)) mod p)
           = eval127 (tomont127 z) mod p); [auto|].
        do 2 rewrite H.
        repeat rewrite eval_tomont_inv; try reflexivity;
        [destruct y| destruct x]; simpl; rewrite inZnZ; apply Z_mod_lt; thisauto.
        - pose proof WordByWordMontgomery.encodemod_correct 64 2 p (2 ^ 63) 1. apply H;
          try ( unfold p, c, s; simpl; unfold Z.pow_pos; simpl; auto with zarith; lia).
          destruct x. simpl. rewrite inZnZ. apply Z_mod_lt. unfold p, c, s; simpl; lia.
        - unfold tomont127.
          pose proof WordByWordMontgomery.encodemod_correct 64 2 p (2 ^ 63) 1. apply H;
          try ( unfold p, c, s; simpl; unfold Z.pow_pos; simpl; auto with zarith; lia).
          destruct y. simpl. rewrite inZnZ. apply Z_mod_lt. unfold p, c, s; simpl; lia.
Qed.

Theorem mul127_corr: forall x y, (eval127((tomont127 (val p x)) *p (tomont127 (val p y))) zmod p) = (eval127 (tomont127 (val p x)) zmod p).
Proof.
    unfold eval127, tomont127. Abort.

Add Field fp : (FZpZ p p_prime).
Theorem mul_correct: forall x y, evalFp2 (mulFp2 (tomontFp2 x) (tomontFp2 y)) = mulp2 p x y.
Proof.
    intros x y. unfold mulFp2, mulp2. simpl. apply Fp2irr.
    simpl. apply zirr. unfold eval127. rewrite WordByWordMontgomery.eval_submod with (r' := 2 ^ 63).
        - Search (((?n1 mod ?n3) * (?n2 mod ?n3)) mod ?n3 ). rewrite Zminus_mod.
          repeat rewrite WordByWordMontgomery.eval_mulmod with (r' := 2^63).
            + unfold tomont127. rewrite Z.mul_mod. rewrite WordByWordMontgomery.eval_encodemod with (r' := 2 ^ 63).
              rewrite WordByWordMontgomery.eval_encodemod with (r' := 2 ^ 63).
              pose proof (Z.mul_mod (@WordByWordMontgomery.eval 64 2
              (WordByWordMontgomery.from_montgomerymod 64
                 2 p 1
                 (WordByWordMontgomery.encodemod 64 2 p 1
                    (val p (snd x))))) ( @WordByWordMontgomery.eval 64 2
                    (WordByWordMontgomery.from_montgomerymod 64
                       2 p 1
                       (WordByWordMontgomery.encodemod 64 2 p 1
                          (val p (snd y))))) p). rewrite H.
                          rewrite WordByWordMontgomery.eval_encodemod with (r' := 2 ^ 63).
              rewrite WordByWordMontgomery.eval_encodemod with (r' := 2 ^ 63).
              rewrite <- Z.mul_mod. rewrite <- Z.mul_mod. rewrite <- Zminus_mod. rewrite quad_res_minus_1.
              ring_simplify. unfold mul. assert ((-1 zmod p) = opp p (1 zmod p)). auto. simpl. simpl. ring. 
    unfold tomont127. rewrite mul_correct. 
Qed.


Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.


Local Existing Instance ToString.C.OutputCAPI.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : emit_primitives_opt := true.


(*
Lemma s_nz: s <> 0.
Proof. unfold s; auto with zarith. Qed.

Lemma m_nz: s - Associational.eval c <> 0.
Proof. unfold s, c; simpl; auto with zarith. Qed.

Definition force_carry l := (Positional.chained_carries w 3 s c l [0%nat;1%nat;2%nat]).

Definition m' := 1.
Definition r := 2 ^ 64.

Lemma m'_correct : (p * m') mod r = (-1) mod r.
Proof. auto with zarith. Qed.
*) *)