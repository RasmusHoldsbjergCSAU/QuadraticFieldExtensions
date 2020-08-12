Require Import ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import List.
Require Import Lia.
Require Import Field.
From Coqprime Require Import UList.
From Coqprime Require Import GZnZ.

Section Fp2.

Variable p: Z.
Hypothesis p_prime: prime p.
Hypothesis p_odd: 2 < p.

Notation "x +p y" := (add p x y) (at level 100).
Notation "x *p y" := (mul p x y) (at level 90).
Notation "x -p y" := (sub p x y) (at level 100).
Notation "x /p y" := (div p x y) (at level 90).

Definition Quad_non_res: znz p :=
match (p mod 4 =? 3) with
  | true => mkznz p ((-1) mod p) (modz p (-1))
  | false =>
  match (p mod 8 =? 3) with
    | true => mkznz p (2 mod p) (modz p 2)
    | false => mkznz p ((-2) mod p) (modz p (-2))
  end
end.

Notation "\beta" := Quad_non_res.

Structure Fp2: Set:=
  mkFp2 { v1: znz p;
          v2: znz p}.

Theorem Fp2irr : forall x1 x2 y1 y2,
  x1 = y1 -> x2 = y2 -> mkFp2 x1 x2 = mkFp2 y1 y2.
Proof. intros. subst x1. subst x2. reflexivity. Qed. 

(* Defining Ring Structure of Fp2 *)

Definition zerop2 := mkFp2 (zero p) (zero p).

Definition onep2 := mkFp2 (one p) (zero p).

Definition addp2 x1 x2 :=
  mkFp2 ( v1 x1 +p v1 x2 ) (v2 x1 +p v2 x2).

Definition subp2 x1 x2 :=
  mkFp2 (v1 x1 -p v1 x2) (v2 x1 -p v2 x2).

Definition mulp2 x1 x2 :=
  mkFp2 (v1 x1 *p v1 x2 +p \beta *p v2 x1 *p v2 x2)
        (v1 x1 *p v2 x2 +p v2 x1 *p v1 x2).
  
Definition oppp2 x := mkFp2 (opp p (v1 x)) (opp p (v2 x)).

Add Field Fp : (FZpZ p p_prime).

Definition RFp2: ring_theory zerop2
  onep2 addp2 mulp2 subp2 oppp2 (@eq Fp2).
Proof.
  split;
  intros; case x; intros; refine (Fp2irr _ _ _ _ _ _);
  unfold zerop2, onep2, mulp2, oppp2, addp2, subp2;
  simpl; field.
Qed.

(* Definining additional field structure *)

Definition invp2 x :=
match ((val p (v1 x)) =? 0) with
  | true =>
     mkFp2 (zero p) (inv p (v2 x *p \beta))
   |false => 
     mkFp2 ( one p +p ( (v2 x *p \beta) /p (v1 x *p (v1 x *p v1 x -p v2 x *p v2 x *p \beta)) ) )
           ( opp p (inv p ( v1 x *p v1 x -p v2 x *p v2 x *p \beta )) )
end.

Definition divp2 x1 x2 := mulp2 x1 (invp2 x2).

Definition FFp2: field_theory zerop2 onep2 addp2 mulp2
  subp2 oppp2 divp2 invp2 (@eq Fp2).
Proof.
  split.
  - apply RFp2.
  - intros H. injection H. rewrite Zmod_small. rewrite Zmod_small.
    auto with zarith. auto with zarith. auto with zarith.
  - intros. unfold divp2. reflexivity.
  - intros. destruct (val p (v1 p0) =? 0) eqn:eq1.
    + unfold invp2, mulp2, onep2. rewrite eq1. simpl.
    refine (Fp2irr _ _ _ _ _ _). field.
    Abort.
    









End Fp2.