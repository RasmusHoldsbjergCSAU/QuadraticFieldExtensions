Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import ZArith Znumtheory List.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Coqprime.Z.Pmod.
Require Import Lia.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Stringification.IR.
Require Import Theory.QuadraticFieldExtensions.
Require Import Coqprime.elliptic.GZnZ.
Require Import Field_theory.
Require Import Ring_theory.
Require Import Crypto.Util.LetIn.
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
From Coqprime Require Import LucasLehmer.
Import ListNotations.
Import Language.Compilers Stringification.C.Compilers.
Import Compilers.API.
Import Associational Positional.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Reifiable implementations of addition and multiplication in Fp2 with p = 2^127 - 1.
   We represent elements af Fp2 as integers in montgomery form; proofs of correctness are included.*)

(*Definitions and notation*)


Definition s := (2 ^ 127)%Z.
Definition c := [(1, 1)].
Definition bitwidth := 64.
Definition p := Eval compute in (s - Associational.eval c).
Eval native_compute in p.
Definition w := uweight bitwidth.
Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).
Definition n := 2%nat.
Definition r := 2^bitwidth.
Definition r' := Eval compute in (val p (GZnZ.inv p (r zmod p))).
Definition m' := Eval compute in (val r (GZnZ.inv r ((- p) zmod r))).

Eval compute in (m').
Lemma r'_correct: (r * r') mod p = 1.
Proof. auto. Qed.

Lemma m'_correct: (p * m') mod r = (-1) mod r.
Proof. auto. Qed.

(*A few results on prime and base field.*)
Lemma p_ge2: 2 < p.
Proof. unfold p; lia. Qed.

Lemma quad_res_minus_1: Quad_non_res p = ((-1) zmod p).
Proof. reflexivity. Qed.

Lemma pmod: p mod 4 =? 3 = true.
Proof. apply Z.eqb_eq; auto. Qed.

Lemma p_prime: (prime p).
Proof. Admitted.
   (*assert (p = Mp 127) as Hmp by reflexivity. rewrite Hmp. 
    exact (LucasTest 127 (refl_equal _)). 
Qed. *)

Notation "x +Fp y" := (GZnZ.add p x y) (at level 100).
Notation "x *Fp y" := (GZnZ.mul p x y) (at level 90).
Notation "x -Fp y" := (GZnZ.sub p x y) (at level 100).

(*Base field arithmetic, encoding and decoding*)
Definition mulp x y := WordByWordMontgomery.mulmod 64 2 p 1 x y.
Definition addp x y := WordByWordMontgomery.addmod 64 2 p x y.
Definition subp x y := WordByWordMontgomery.submod 64 2 p x y.
Definition tomont z := WordByWordMontgomery.encodemod bitwidth n p m' z.
Definition evalp z := @WordByWordMontgomery.eval bitwidth n (WordByWordMontgomery.from_montgomerymod bitwidth n p m' z).

Local Notation "x '+p' y" := (addp x y) (at level 100).
Local Notation "x *p y" := (mulp x y) (at level 90).
Local Notation "x -p y" := (subp x y) (at level 100).


(*Extended field arithmetic encoding and decoding*)
Definition addFp2 := fun x y => ((fst x) +p (fst y), (snd x) +p (snd y)).
(*
Definition mulFp2 := fun x y => let '(x1, x2) := x in
    let '(y1, y2) := y in
    dlet v0 := (x1) *p (y1) in
        dlet v1 := (x2) *p (y2) in
            (
                v0 -p v1,
                ((((x1) +p (x2)) *p ((y1) +p (y2))) -p v0) -p v1
            ).
*)

            Definition subFp2 := fun x y => ((fst x) -p (fst y), (snd x) -p (snd y)). 

Definition mulFp2 := fun x y => let '(x1, x2) := x in
    let '(y1, y2) := y in
    (
        (x1 *p y1) -p (x2 *p y2),
        (x1 *p y2) +p (x2 *p y1)
    ).
 

Definition tomontFp2:= fun x => (tomont (val p (fst x)), tomont (val p (snd x))).
Definition evalFp2:= fun x => (evalp (fst x) zmod p, evalp (snd x) zmod p).


(*A few auxillary results on field arithmetic*)
Add Field fp : (FZpZ p p_prime).
Lemma Fp2_opp_sub_equiv: forall x y z w, (x *Fp y +Fp ((-1 zmod p) *Fp z) *Fp w) = (x *Fp y -Fp (z *Fp w)).
Proof. intros. assert (H: (-1 zmod p) = GZnZ.opp p (one p)) by auto; rewrite H; ring. Qed.

Lemma zpz_le_p: forall x, 0 <= val p x < p.
Proof.
    intros [val Hval]; simpl; rewrite Hval; apply Z_mod_lt; unfold p; auto with zarith.
Qed.

Lemma karatsuba_correct: forall x1 x2 y1 y2, ((x1 +Fp x2) *Fp (y1 +Fp y2) -Fp x1 *Fp y1 -Fp x2 *Fp y2) = (x1 *Fp y2 +Fp x2 *Fp y1).
Proof. intros; ring. Qed.



(*Proofs of validity (as in Crypto.Arithmetic.WordByWordMontgomery)*)

Ltac lauto := auto with zarith; try unfold p; try unfold n; try unfold bitwidth; lia.
Lemma tomont_valid: forall x, WordByWordMontgomery.valid bitwidth n p (tomont (val p x)).
Proof.
    intros; unfold tomont; pose proof WordByWordMontgomery.encodemod_correct bitwidth n p (r') m' as [_ H0].
    1-6: lauto. apply H0; case x; intros; simpl; rewrite inZnZ; apply Z_mod_lt; unfold p; lia.
Qed.

Lemma add_valid: forall x y,WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> WordByWordMontgomery.valid bitwidth n p (x +p y).
Proof.
    intros; pose proof WordByWordMontgomery.addmod_correct bitwidth n p r' m' as [_ H1].
    1-6: lauto. apply H1; auto.
Qed.

Lemma sub_valid: forall x y,WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> WordByWordMontgomery.valid bitwidth n p (x -p y).
Proof.
    intros; pose proof WordByWordMontgomery.submod_correct bitwidth n p r' m' as [_ H1].
    1-6: lauto. apply H1; auto.
Qed.

Lemma mul_valid: forall x y,WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> WordByWordMontgomery.valid bitwidth n p (x *p y).
Proof.
    intros; pose proof WordByWordMontgomery.mulmod_correct bitwidth n p r' m' as [_ H1].
    1-6: lauto. apply H1; auto.
Qed.


(*Correctness of evaluation wrt. operations and encoding*)
Theorem eval_tomont_inv: forall val, 0 <= val < p -> evalp (tomont val) mod p = val.
Proof.
    intros val H; unfold evalp, tomont; rewrite WordByWordMontgomery.eval_encodemod with (r' := r'); try lauto.
Qed.

Lemma eval_sub: forall x y, WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> (evalp (x -p y)) mod p = ( evalp x - evalp y ) mod p.
Proof. intros; unfold evalp; rewrite WordByWordMontgomery.eval_submod with (r' := r'); lauto. Qed.

Lemma eval_add: forall x y, WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> (evalp (x +p y)) mod p = ( evalp x + evalp y ) mod p.
Proof. intros; unfold evalp; rewrite WordByWordMontgomery.eval_addmod with (r' := r'); lauto. Qed.

Lemma eval_mul: forall x y, WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> (evalp (x *p y)) mod p = ( evalp x * evalp y ) mod p.
Proof. intros; unfold evalp; rewrite WordByWordMontgomery.eval_mulmod with (r' := r'); lauto. Qed.

Lemma eval_sub_mod: forall x y, WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> (evalp (x -p y)) mod p = ( evalp x mod p - evalp y mod p ) mod p.
Proof. intros; rewrite eval_sub; try assumption; apply Zminus_mod. Qed.

Lemma eval_add_mod: forall x y, WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> (evalp (x +p y)) mod p = ( evalp x mod p + evalp y mod p ) mod p.
Proof. intros; rewrite eval_add; try assumption; apply Z.add_mod; unfold p; auto with zarith. Qed.

Lemma eval_mul_mod: forall x y, WordByWordMontgomery.valid bitwidth n p x -> WordByWordMontgomery.valid bitwidth n p y -> (evalp (x *p y)) mod p = ( evalp x mod p * (evalp y mod p) ) mod p.
Proof. intros; rewrite eval_mul; try assumption; apply Z.mul_mod; unfold p; auto with zarith. Qed.


(*Correctness of extended field operations and encoding*)
Theorem addFp2_correct: forall x y, evalFp2 (addFp2 (tomontFp2 x) (tomontFp2 y)) = addp2 p x y.
Proof.
    intros; apply Fp2irr; simpl; apply zirr; rewrite eval_add_mod; try apply tomont_valid;
    rewrite 2!eval_tomont_inv; auto; apply zpz_le_p.
Qed.

Theorem subFp2_correct: forall x y , evalFp2 (subFp2 (tomontFp2 x) (tomontFp2 y)) = subp2 p x y.
Proof.
    intros; apply Fp2irr; simpl; apply zirr; rewrite eval_sub_mod; try apply tomont_valid;
    rewrite 2!eval_tomont_inv; auto; apply zpz_le_p.
Qed.

Theorem mul_correct: forall x y, evalFp2 (mulFp2 (tomontFp2 x) (tomontFp2 y)) = mulp2 p x y.
Proof.
    intros x y. unfold mulFp2, mulp2. rewrite quad_res_minus_1. simpl. apply Fp2irr.
    - simpl; rewrite Fp2_opp_sub_equiv; apply zirr; rewrite eval_sub_mod; try (apply mul_valid; apply tomont_valid);
      rewrite 2!eval_mul_mod; try apply tomont_valid; rewrite 4!eval_tomont_inv; try apply zpz_le_p; reflexivity.
    - apply zirr. rewrite Prod.snd_pair. rewrite eval_add_mod.
      rewrite 2!eval_mul_mod. rewrite 4!eval_tomont_inv; try apply zpz_le_p. reflexivity.
      1, 2, 3, 4: apply tomont_valid.
      1, 2 : apply mul_valid; apply tomont_valid.
Qed.

Theorem to_montFp2_correct: forall x y, evalFp2 (tomontFp2 (x, y)) = (x, y).
Proof.
    intros x y; apply injective_projections; [case x | case y];
    intros val Hval; apply zirr; simpl; apply eval_tomont_inv;
    rewrite Hval; apply Z_mod_lt; unfold p; simpl; lia.
Qed.

(*Reification and subsequent printing to C of field operations.
  Note that a slightly altered implementation of operations are used;
  their equivalence is shown below. *)
Definition  mulFp2SBr x1 x2 y1 y2 :=
        dlet v0 := (x1) *p (y1) in 
        dlet v1 := (x2) *p (y2) in
        dlet v2 := (x1) *p (y2) in
        dlet v3 := (x2) *p (y1) in
        (
            v0 -p v1,
            v2 +p v3
        ).

Lemma mulFp2SBr_correct: forall x y, mulFp2SBr (fst x) (snd x) (fst y) (snd y) = mulFp2 x y.
Proof. intros [] []; auto. Qed.

Definition addFp2r x1 x2 y1 y2 := (x1 +p y1, x2 +p y2).

Lemma addFp2r_correct: forall x y, addFp2r (fst x) (snd x) (fst y) (snd y) = addFp2 x y.
Proof. auto. Qed.

Definition subFp2r x1 x2 y1 y2 := (x1 -p y1, x2 -p y2).

Lemma subFp2r_correct: forall x y, subFp2r (fst x) (snd x) (fst y) (snd y) = subFp2 x y.
Proof. auto. Qed.

(*Initializing parameters for reification*)
(* Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.
Local Existing Instance ToString.C.OutputCAPI.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : emit_primitives_opt := true.

Compute
     (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_addFp2_"
     false None [1; 64; 128] 64
     ltac:(let r := Reify (addFp2r) in
           exact r)
           (fun _ _ => [])
           (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt))))%zrange
           (Some (repeat (Some r[0~>2^64 - 1]) 2), Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange).

Compute
     (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_subFp2_"
     false None [1; 64; 128] 64
     ltac:(let r := Reify (subFp2r) in
           exact r)
           (fun _ _ => [])
           (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt))))%zrange
           (Some (repeat (Some r[0~>2^64 - 1]) 2), Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange).

Compute
     (Pipeline.BoundsPipelineToString
        "fiat_" "fiat_mulFp2_"
        false None [1; 64; 128] 64
        ltac:(let r := Reify (mulFp2r) in
              exact r)
              (fun _ _ => [])
              (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt))))%zrange
              (Some (repeat (Some r[0~>2^64 - 1]) 2), Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange).

(* The generated code makes calls to the functions; fiat_cmovznz_u64,
   fiat_addcarryx_u64, fiat_subborrowx_u64 and fiat_mulx_u64.
   These can be generated with the following.*)

Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_cmovznz_u64"
        true None [1; 64; 128] 64
        ltac:(let r := Reify (cmovznz 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1])%zrange).

Compute
    (Pipeline.BoundsPipelineToString
        "fiat_" "fiat_subborrowx_u64"
            true None [1; 64; 128] 64
            ltac:(let r := Reify (subborrowx 64) in
             exact r)
                (fun _ _ => [])
                (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
                (Some r[0~>2^64-1], Some r[0~>1])%zrange).

Compute
(Pipeline.BoundsPipelineToString
   "fiat_" "fiat_addcarryx_u64"
      true None [1; 64; 128] 64
      ltac:(let r := Reify (addcarryx 64) in
            exact r)
             (fun _ _ => [])
             (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
             (Some r[0~>2^64-1], Some r[0~>1])%zrange).

Compute
(Pipeline.BoundsPipelineToString
   "fiat_" "fiat_mulx_u64"
      true None [1; 64; 128] 64
      ltac:(let r := Reify (mulx 64) in
            exact r)
             (fun _ _ => [])
             (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt))%zrange
             (Some r[0~>2^64-1], Some r[0~>2^64-1])%zrange). *)