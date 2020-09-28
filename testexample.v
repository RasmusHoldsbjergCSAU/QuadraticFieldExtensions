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

Local Existing Instance ToString.C.OutputCAPI.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : emit_primitives_opt := true.

Definition addm x y := (WordByWordMontgomery.addmod 64 2 (2^127 - 1) x y).

Definition testfunction (l1 l2 l3 : list Z) :=addm (addm l1 l2) l3.

Compute
     (Pipeline.BoundsPipelineToStrings
     "fiat_" "fial_add_"
        true None [64; 128] 64
        ltac:(let r := Reify (testfunction) in
              exact r)
              (fun _ _ => [])
              (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt)))%zrange
              (Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange).