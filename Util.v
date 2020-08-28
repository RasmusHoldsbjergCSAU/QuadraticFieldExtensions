Require Import ZArith Znumtheory.
From Coq Require Import Field.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Pmod.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Znat.
Require Import Lia.

Section Field.
    Context {F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv}
            {std_field: @field_theory F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (@eq F)}.

    Add Field F : std_field.

    Instance std_to_fiatCrypto_field : @field F (@eq F) Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv.
    Proof.
        repeat split; try apply (Finv_l (std_field));
        try (unfold not; intros H; symmetry in H; apply (F_1_neq_0 std_field) in H; auto);
        try apply (Fdiv_def std_field); try apply (_ (std_field));
        intros; simpl; try field.
    Qed.
End Field.

Section Characteristic.

Context {n : Z}.
Notation "x + y" := (add n x y).
Notation "x 'zmod' n" := (mkznz n (x mod n) (modz n x)) (at level 90).


Section RZnZ.

Context {n_pos: 0 < n}.

Lemma Z_pos: exists (npos : positive), Zpos npos = n.
Proof.
induction n as [ |p| ]; try discriminate. exists p; reflexivity.
Qed.


Check char_ge.

Require Import Coq.PArith.BinPos.

Check Pos.peano_case.

Check ex_proj1.

Check @char_ge (znz n)%type (@eq (znz n)) (zero n) (one n) (opp n) (add n) (sub n) (mul n).

Notation char_znz_n_ge := (@char_ge (znz n)%type (@eq (znz n)) (zero n) (one n) (opp n) (add n) (sub n) (mul n)).

Check char_znz_n_ge.

Lemma Char_geq_n: forall npos, n = Zpos npos ->
char_znz_n_ge npos.
Proof.
    Check Pos.peano_case ().
    apply Pos.peano_case.
    generalize dependent npos.
    -
    intros npos Hn. unfold char_ge, Hierarchy.char_ge. intros x Hx contra.
    remember (Pos.to_nat npos) as nnat eqn:Hnat.
    induction (nnat).
        - apply (f_equal (fun y => )). 
Qed.










Context {p}
        {p_prime: prime p}.

Notation Fp := (znz p).
Notation FFp := (FZpZ p p_prime).



Check char_ge.

Lemma Char_geq_p :forall (n : positive), n < p ->
@char_ge (znz p)%type (@eq (znz p)) (zero p) (one p) (opp p) (add p) (sub p) (mul p) n.
Proof.
    intros n H. remember (Pos.to_nat n) as nnat eqn:Hn. induction (nnat).
    - unfold char_ge, Hierarchy.char_ge. intros x Hx contra. simpl in contra. 
    
    
    
    unfold char_ge, Hierarchy.char_ge. intros x H0 contra. simpl in contra.
    assert (of_nat(Pos.to_nat x) (Rzero := zero p) (Radd := add p) (Rone := one p) = (x zmod p) ).
    -   remember (Pos.to_nat x) as x_nat eqn:Hx.
        generalize dependent x.
        induction (x_nat). simpl. intros.
        apply (f_equal (fun y => Z.of_nat y)) in Hx. rewrite positive_nat_Z in Hx. simpl in Hx.
        rewrite <- Hx. auto.
        +   intros x0 Hge Hn0. simpl.
            assert (of_nat n0 (Rzero := zero p) (Radd := add p) (Rone := one p) = (Z.pred(x0) zmod p)).
                * apply (f_equal (fun y => Nat.pred y)) in Hn0. simpl in Hn0.
                  destruct (Z.pred x0); try contradiction. 

End Characteristic.