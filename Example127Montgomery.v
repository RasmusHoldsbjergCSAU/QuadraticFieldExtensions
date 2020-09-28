Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import ZArith Znumtheory List.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
From Coqprime Require Import Pmod.
Require Import Lia.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Stringification.IR.
Require Import QuadraticFieldExtensions.
Require Import Coqprime.elliptic.GZnZ.

Import ListNotations.

Definition s := (2 ^ 127)%Z.
Definition c := [(1, 1)].
Definition p := Eval compute in (s - Associational.eval c).
Hypothesis p_prime: prime p.
Hypothesis p_ge2: 2 < p.
Hypothesis pmod: p mod 4 =? 3 = true.
Definition w := uweight 64.
Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).
Check QuadraticFieldExtensions.Quad_non_res.
Lemma quad_res_minus_1: Quad_non_res p = ((-1) zmod p).
Proof.
    reflexivity.
Qed.

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
*)

Check WordByWordMontgomery.from_montgomerymod 64 2 p 4.

Definition mul127 x y := (WordByWordMontgomery.mulmod 64 2 p 1 x y).
Definition add127 x y := (WordByWordMontgomery.addmod 64 2 p x y).
Definition sub127 x y := (WordByWordMontgomery.submod 64 2 p x y).
Definition enc127 z := Positional.encode w 2 s c z.
Definition tomont127 z := WordByWordMontgomery.encodemod 64 2 p 1 z.
Definition eval127' z := (Positional.eval w 2 z).
Definition frommont127 z := WordByWordMontgomery.from_montgomerymod 64 2 p 1 z.
Definition eval127 z := @WordByWordMontgomery.eval 64 2 (WordByWordMontgomery.from_montgomerymod 64 2 p 1 z).



(** * Push-Button Synthesis Examples *)
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

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional.

Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.
(*
Check mulmod.
Check (weight 51 1).
Check w.

About mulmod.

Check mulmod w s c 2.
Check mul127.
(*
Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f g => mul127 f g) in
              exact r)
               (Some (repeat (@None _) 2), ((Some (repeat (@None _) 2), tt)))
               ZRange.type.base.option.None).
*)
Check addcarryx 64.
Check mul127.

Check hd.
Check tl.

About WordByWordMontgomery.mulmod.
Definition mp := 10540996613548314624%Z.

Eval compute in ((( 7 * mp)) mod 2 ^ 64) - 2^64.

Definition mmod := WordByWordMontgomery.mulmod 64 1 7 mp.

Check mmod.

Definition reifiablemul127 x1 x2 y1 y2 := (let prod := mul127 [x1; x2] [y1; y2] in (hd prod, hd (tl prod))). 

Definition testfun (x y : Z) := ((mmod [x] [y]), x).

Check testfun.


*)

Local Existing Instance ToString.C.OutputCAPI.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : emit_primitives_opt := true.
(*
Eval compute in ((-7905747460161236992) mod 2^64).

Definition mp := 10540996613548314624%Z.

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_mul127_u64"
        true None [1] 64
        ltac:(let r := Reify (testfun) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt))%zrange
               (None, Some r[0~>2^64 - 1])%zrange).


*)
Local Notation "x '+p' y" := (add127 x y) (at level 100).
Local Notation "x *p y" := (mul127 x y) (at level 90).
Local Notation "x -p y" := (sub127 x y) (at level 100).

Require Import Crypto.Util.LetIn.

Definition addFp2 := fun x y => ((fst x) +p (fst y), (snd x) +p (snd y)).
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


Compute
     (Pipeline.BoundsPipelineToStrings
        "fiat_" "fial_mulFp2_"
        false None [64; 128] 64
        ltac:(let r := Reify (mulFp2r) in
              exact r)
              (fun _ _ => [])
              (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt))))%zrange
              (Some (repeat (Some r[0~>2^64 - 1]) 2), Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange).


Definition to_montgomeryFp2 x := (tomont127 (val p (fst x)), tomont127 (val p (snd x))).


Definition eval_Fp2 x :=
    (
        eval127(fst x) zmod p,
        eval127(snd x) zmod p
    ).



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



(*testing*)

Definition z1 := 2 ^ 64 + 1.
Definition z2 := 2 ^ 64.
Definition elem1 := enc127 z1.
Definition elem2 := enc127 z2.
Definition mon1 := tomont127 z1.
Definition mon2 := tomont127 z2.

Definition prod := mon1 *p mon2.
Definition sum := mon1 +p mon2.

(*Eval compute in (elem1).*)
Eval compute in (mon1).
Eval compute in (frommont127 mon1).
Eval compute in (eval127 mon1).
Eval compute in (z1).

Eval compute in prod.
Eval compute in (frommont127 prod).
Eval compute in (eval127 prod).
Eval compute in (z1 * z2 mod p).