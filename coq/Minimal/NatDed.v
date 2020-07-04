Require Import
        Arith_base
        List
        Minimal.Syntax
        Minimal.SequentCalculus
        Tactics.Tactics
        Utils.Basics.

(** natural deduction system *)


Inductive nat_ded : ctx -> form -> Prop :=
| Id_Nd G a
  : a el G -> nat_ded G a
| ExFalsum G a
  : nat_ded G Falsum -> nat_ded G a
| Implies_I G a b
  : nat_ded (a :: G) b -> nat_ded G (Implies a b)
| Implies_E G a b
  : nat_ded G (Implies a b) -> nat_ded G a -> nat_ded G b.

Hint Constructors nat_ded : core.

Lemma nat_ded_reflexivity : Reflexivity nat_ded.
Proof.
  intros G a.
  auto.
Qed.

Lemma nat_ded_monotonicity : Monotonicity nat_ded.
Proof.
  intros G G' a H H1. revert G' H. induction H1; intros G' D; eauto.
Qed.

Lemma nat_ded_weakening G G1 a : nat_ded G a -> G <<= G1 -> nat_ded G1 a.
Proof.
  intros C D.
  apply nat_ded_monotonicity with (G := G); auto.
Qed.

Lemma nat_ded_cut : forall G a b, nat_ded G a -> nat_ded (a :: G) b -> nat_ded G b.
Proof.
  intros G a b H H1.
  eauto.
Qed.

Lemma nat_ded_cut_and_weak G a b : nat_ded G a -> nat_ded [a] b -> nat_ded G b.
Proof.
  intros D E.
  apply nat_ded_cut with (a := a) ; auto.
  apply (nat_ded_weakening E).
  auto.
Qed.

(** Equivalence of nat_ded and seq_calc *)

Lemma seq_calc_implies_nat_ded G a : seq_calc G a -> nat_ded G a.
Proof.
  intros C.
  induction C ; eauto.
Qed.

Lemma nat_ded_implies_seq_calc G a : nat_ded G a -> seq_calc G a.
Proof.
  intros C. induction C; eauto.
  -
    apply seq_calc_falsum ; auto.
  -
    apply seq_calc_implies in IHC1. apply admissibility with (a := a); auto.
Qed.

Theorem seq_calc_iff_nat_ded G a : seq_calc G a <-> nat_ded G a.
Proof.
  split.
  apply seq_calc_implies_nat_ded.
  apply nat_ded_implies_seq_calc.
Qed.

Corollary nat_ded_consistent : exists a, ~ nat_ded [] a.
Proof.
  exists Falsum. intros H.
  apply nat_ded_implies_seq_calc in H.
  apply seq_calc_no_falsum in H ; auto.
Qed.
