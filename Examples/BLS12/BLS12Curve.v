Require Import Lia.
Require Import Crypto.Curves.Weierstrass.Projective.
From Coq Require Import Field.
From Coqprime Require Import GZnZ.
Require Import ZArith Znumtheory.
From Coqprime Require Import Pmod.
Require Import Theory.FieldsUtil.
Require Import Theory.RingsUtil.
Require Import Crypto.Util.Decidable.

Section BLS12Curve1.

    Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).

    Definition u := -0xd201000000010000.
    Definition p_of_u u := (((u - 1)^2 * (u^4 - u^2 + 1)) / 3) + u.
    Definition p := Eval compute in (p_of_u u).
    Hypothesis p_prime : prime p.
    Definition F := znz p.
    Definition Feq := @eq F.
    Definition Fzero := zero p.
    Definition Fone := one p.
    Definition Fopp := opp p.
    Definition Fadd := add p.
    Definition Fsub := sub p.
    Definition Fmul := mul p.
    Definition Finv := inv p.
    Definition Fdiv := div p.
    Definition a := Fzero.
    Definition b := 4 zmod p.

    Add Field Fp : (FZpZ p p_prime).

    Lemma p_ge_3: 3 < p.
    Proof. unfold p. lia. Qed.   

    Definition field := @std_to_fiatCrypto_field F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (FZpZ p p_prime).

    Definition char_ge_3 := @Char_geq_p p 3 p_ge_3.


    Lemma Feq_dec: DecidableRel Feq.
    Proof.
        intros. case x as [xval Hx], y as [yval Hy]. destruct (xval =? yval) eqn:case.
            - rewrite Z.eqb_eq in case. left. apply zirr. auto.
            - rewrite Z.eqb_neq in case. right. unfold not. intros. inversion H as [H1]. contradiction.
    Qed.

    Notation "x +p y" := (add p x y) (at level 100).
    Notation "x *p y" := (mul p x y) (at level 90).
    Notation "x -p y" := (sub p x y) (at level 100).
    Notation "x /p y" := (div p x y) (at level 90).
    Notation "n 'zmod' p" := (mkznz p (n mod p) (modz p n)) (at level 90).


    Definition three_b : F := (b +p b +p b).
    Lemma three_b_correct : (three_b = (b +p b +p b)).
    Proof. auto. Qed.
    Check three_b_correct.
    Local Notation "4" := (Fone +p Fone +p Fone +p Fone).
    Local Notation "27" := ((4 *p 4) +p 4 +p 4 +p Fone +p Fone +p Fone).
    Lemma discriminant_nonzero: id(((4 *p a *p a *p a) +p (27 *p b *p b)) <> Fzero).
    Proof.
        intros contra; inversion contra.
    Qed.
    

    Check @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul.

    Lemma char_ge_21: @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (21%positive).
    Proof.
        pose proof @Char_geq_p p 21; assert (21 < p) by (unfold p; lia); auto.
    Qed.
    


    Check  @Projective.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3
            Feq_dec three_b three_b_correct discriminant_nonzero char_ge_21.




    Definition point := @Projective.point F Feq Fzero Fadd Fmul a b.

    Definition eq (x y : point) := @Projective.eq F Feq Fzero Fadd Fmul a b Feq_dec x y.

    Definition opp (x : point) := @Projective.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec x.

    Definition thisP := (0 zmod p, 2 zmod p, 0 zmod p).
(*
    Definition point_cond1 X Y Z := (Y *p Y *p Z) = (X *p X *p X +p a *p X *p Z *p Z +p b *p Z *p Z *p Z).

    Check point_cond1.

    Definition point_cond2 Y Z :=
        Z = Fzero -> Y <> Fzero.

    Definition P_correct P := let '(X, Y, Z) := P in
        (point_cond1 X Y Z) /\ (point_cond2 Y Z).

    Lemma thisPcorrect: P_correct thisP.
    Proof.
        simpl. split.
            - assert (H: Fzero = (0 zmod p)) by auto. rewrite <- H. auto.
            - discriminate.
    Qed.
*)

    Variable myP : point.

    Program Definition thiseq (P Q : point) : Prop :=
        (@Projective.eq F Feq Fzero Fadd Fmul a b Feq_dec P Q).

    Program Definition thisopp (P : point) : point :=
        (@Projective.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec P).


    Program Definition thisadd (P Q: point) (except : Projective.not_exceptional P Q) : point :=
        (@Projective.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3
        Feq_dec three_b three_b_correct discriminant_nonzero char_ge_21) P Q except.

End BLS12Curve1.


