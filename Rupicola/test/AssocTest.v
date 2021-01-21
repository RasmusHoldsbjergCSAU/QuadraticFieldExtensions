Require Import Rupicola.Examples.Assoc.Assoc.
Require Import bedrock2.ToCString.
From Coq Require Import String.
Require Import Coq.Strings.Ascii.
Open Scope string_scope.
Require Import List.
Import List.ListNotations.

Definition asd : Coq.Strings.String.string := (c_module [Bedrock2.assoc_found]).

 Check Bedrock2.assoc_found.
 About Bedrock2.assoc_found.
Redirect "test.c" Eval compute in asd.