Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.CondSwap.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation.
Require Import Crypto.Bedrock.Group.Point.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.ScalarField.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import bedrock2.Semantics.
Require Import bedrock2.ToCString.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Coqprime.elliptic.GZnZ.


Coercion expr.var : string >-> Syntax.expr.
Unset Printing Coercions.
Local Open Scope bedrock_expr.
Local Open Scope Z_scope.
Local Open Scope F_scope.

Require Import bedrock2.BasicC64Semantics.


Print FieldParameters.
Definition thism : positive := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.
Definition a : Z := 23223.
Definition toF n := (F.of_Z thism n).


Instance field_parameters : FieldParameters :=
{
    M_pos := thism;
    a24 := toF a;
    mul := "mul";
    add := "add";
    sub := "sub";
    square := "square";
    scmula24 := "scmula24";
    inv := "inv";
    from_bytes := "from_bytes";
    to_bytes := "to_bytes";
    felem_copy := "felem_copy";
    felem_small_literal := "felem_small_literal"
}.

Hypothesis m_prime: Znumtheory.prime (Z.pos M_pos).

Instance field_parameters_ok : FieldParameters_ok :=
{
    M_prime := m_prime
}.

Check mem.
Instance field_representation : FieldRepresentation :=
{
    felem := Z;
    feval := toF;
    feval_bytes l := toF 10;
    felem_size_in_bytes := 48;
    FElem (w : word) (f : Z) (m : mem) := True; 
    bounds := Z; 
    bounded_by b f := False;
    loose_bounds := 100;
    tight_bounds := 100
    }.

    About Placeholder.
    Check Placeholder.
Instance field_representation_ok : FieldRepresentation_ok.
Proof.
    constructor; try auto.
        - intros. split; intros.
            + exists (12). simpl. auto.
            + inversion H. simpl in H0. unfold Placeholder.

Definition bedrock_func : Type :=
    string * (list string * list string * cmd).

    Definition mont_ladder : bedrock_func :=
        ("mont_ladder",
         (["arg1"; "arg2"; "arg3"],
          ["out1"; "out2"],
          montladder_body)).

Print montladder_body.
Check montladder_body.
Check c_func.
Check c_module.