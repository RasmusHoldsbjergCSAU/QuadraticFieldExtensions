Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import ZArith Znumtheory List.
From Coqprime Require Import Pmod.
Require Import Lia.
Require Import Crypto.Util.LetIn.

Import ListNotations.

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

Definition s := (2 ^ 127)%Z.
Definition c := [(1, 1)].
Definition p := s - Associational.eval c.
Definition w := weight 85 2.


(*
Lemma s_nz: s <> 0.
Proof. unfold s; auto with zarith. Qed.

Lemma m_nz: s - Associational.eval c <> 0.
Proof. unfold s, c; simpl; auto with zarith. Qed.
*)

Definition force_carry l := (Positional.chained_carries w 3 s c l [0%nat;1%nat;2%nat]).

Definition mul127 x y := force_carry (Positional.mulmod w s c 3 x y).
Definition add127 x y := force_carry (Positional.add w 3 x y).
Definition sub127 x y := force_carry (Positional.sub w 3 [0; 0; 0] x y).

Notation "x +p y" := (add127 x y) (at level 100).
Notation "x -p y" := (sub127 x y) (at level 100).
Notation "x *p y" := (mul127 x y) (at level 90).


Definition addFp2 := fun x y => (add127 (fst x) (fst y), add127 (snd x) (snd y)).

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

(*testing*)

Definition z1 := 1.
Definition z2 := 8796093022207.
Definition elem1 := (Positional.encode w 3 s c z1).
Definition elem2 := (Positional.encode w 3 s c z2).
Definition product := mul127 elem1 elem2.
Definition sum := add127 elem1 elem2.

Definition test (x1 x2 x3 x4 : list Z) := (x1 +p x2, x2).
(* 
Compute
     (Pipeline.BoundsPipelineToStrings
        "fiat_" "fial_mulFp2_"
        false None [64; 128] 64
        ltac:(let r := Reify (test) in
              exact r)
              (fun _ _ => [])
              (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2), (Some (repeat (Some r[0~>2^64 - 1]) 2) , (Some (repeat (Some r[0~>2^64 - 1]) 2), tt))))%zrange
              (Some (repeat (Some r[0~>2^64 - 1]) 2), Some (repeat (Some r[0~>2^64 - 1]) 2))%zrange). *)
