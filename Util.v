Require Import ZArith Znumtheory.
From Coq Require Import Field.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Pmod.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Znat.
Require Import Lia.

Section Ring.
    Context {R Rzero Rone Radd Rmul Rsub Ropp}
            {std_ring: @ring_theory R Rzero Rone Radd Rmul Rsub Ropp (@eq R)}.

    Add Ring R : std_ring.

    Instance std_to_fiatCrypto_ring : @ring R (@eq R) Rzero Rone Ropp Radd Rsub Rmul.
    Proof. repeat split; try (intros; ring); try apply (_ (std_ring)). Qed.


End Ring.

Section Field.
    Context {F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv}
            {std_field: @field_theory F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (@eq F)}.

    Add Field F : std_field.

    Instance std_to_fiatCrypto_field : @field F (@eq F) Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv.
    Proof.
        repeat split; try apply (Fdiv_def std_field); try (intros ; field); try apply (_ (std_field)); auto.
        - symmetry. apply (F_1_neq_0 (std_field)).
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


Require Import Coq.PArith.BinPos.
Add Ring Zn : (RZnZ n n_pos).
Notation ZnZ := (RZnZ n n_pos).

Instance ZnZfc : @ring (znz n) (@eq (znz n)) (zero n) (one n) (opp n) (add n) (sub n) (mul n).
Proof. apply @std_to_fiatCrypto_ring, ZnZ. Qed.

Definition n_as_pos (npos : positive): Prop := Zpos npos = n.
Check of_Z.

Notation ZnZ_of_Z := (@of_Z (znz n) (zero n) (one n) (opp n) (add n)). 
Check of_nat.
Notation ZnZ_of_nat := (@of_nat (znz n) (zero n) (one n) (add n)).
Notation char_znz_n_ge := (@char_ge (znz n)%type (@eq (znz n)) (zero n) (one n) (opp n) (add n) (sub n) (mul n)).

About Crypto.Algebra.Hierarchy.char_ge.
Check char_znz_n_ge.

Lemma of_nat_ZnZ : forall m, ZnZ_of_nat m = ((Z.of_nat m) zmod n).
Proof.
    intros. induction m.
        - reflexivity.
        - assert (((Z.of_nat (S m)) zmod n) = add n (Z.of_nat m zmod n) (one n)).
          apply zirr. simpl. rewrite <- Zplus_mod. lia.
          rewrite H. simpl. apply zirr. rewrite IHm. reflexivity.
Qed.


Lemma of_Z_ZnZ : forall m, ZnZ_of_Z m = (m zmod n).
Proof.
    intros m. destruct m.
        - reflexivity.
        - simpl; rewrite of_nat_ZnZ, positive_nat_Z; reflexivity.
        - simpl. rewrite of_nat_ZnZ, positive_nat_Z. unfold opp. apply zirr. simpl.
          assert (Z.neg p = -1 * p) by lia. rewrite H. rewrite Zmult_mod.
          assert (- (p mod n) = -1 * (p mod n)) by lia. rewrite H0. rewrite Zmult_mod.
          rewrite Zmod_mod. reflexivity.
Qed.

Context {p}
        {p_prime: prime p}.

Notation Fp := (znz p).
Notation FFp := (FZpZ p p_prime).



Check char_ge.

Lemma Char_geq_p :forall (n : positive), n < p ->
@char_ge (znz p)%type (@eq (znz p)) (zero p) (one p) (opp p) (add p) (sub p) (mul p) n.
Proof.
    unfold char_ge.
    unfold Hierarchy.char_ge.
    intros m H p0 Hp0.
    remember (Pos.to_nat p0) as p0nat eqn:Hp0'. induction (p0nat).
    - simpl in Hp0'. simpl. Search lt.
    - 
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