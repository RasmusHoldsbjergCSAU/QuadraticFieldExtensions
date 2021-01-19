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
Require Import Crypto.Util.LetIn.
Import ListNotations.


(*Definition, reification and printing to C of multiplication in Fp2, where p is the prime 2^127 - 1.*)

Definition s := (2 ^ 127)%Z.
Definition c := [(1, 1)].
Definition p := Eval compute in (s - Associational.eval c).

Definition mul127 x y := (WordByWordMontgomery.mulmod 64 2 p 1 x y).
Definition add127 x y := (WordByWordMontgomery.addmod 64 2 p x y).
Definition sub127 x y := (WordByWordMontgomery.submod 64 2 p x y).

Local Notation "x '+p' y" := (add127 x y) (at level 100).
Local Notation "x *p y" := (mul127 x y) (at level 90).
Local Notation "x -p y" := (sub127 x y) (at level 100).

Definition addFp2 := fun x y => ((fst x) +p (fst y), (snd x) +p (snd y)).

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

(*Reification and subsequent printing to C of functions.*)
(* 
(*cmovznz*)
Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_cmovznz_u64"
        true None [1; 64; 128] 64
        ltac:(let r := Reify (cmovznz 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1])%zrange).

(*addcarry*)
Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_addcarryx_u64"
        true None [1; 64; 128] 64
        ltac:(let r := Reify (addcarryx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).

(*subborrow*)
Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_subborrowx_u64"
        true None [1; 64; 128] 64
        ltac:(let r := Reify (subborrowx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).


(*mul*)
Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_mulx_u64"
        true None [64; 128] 64
        ltac:(let r := Reify (mulx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt))%zrange
               (Some r[0~>2^64-1], Some r[0~>2^64-1])%zrange).


About Pipeline.BoundsPipelineToString.

(*mulFp2*)
Time Redirect "log" Compute
     (Pipeline.BoundsPipelineToString
        "fiat_" "fiat_mulFp2_"
        false None [1; 64; 128] 64
        ltac:(let r := Reify (mulFp2r) in
              exact r)
              (fun _ _ => [])
              (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt))))%zrange
              (Some (repeat (Some r[0~>2^64 - 1]) 2), Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange). *)
