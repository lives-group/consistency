Require Import
        Arith_base
        List
        Minimal.Syntax
        Tactics.Tactics
        Utils.Basics.


(** sequent calculus definition *)

Inductive seq_calc : ctx -> form -> Prop :=
| Id G a
  : (Var a) el G -> seq_calc G (Var a)
| Falsum_L G a
  : Falsum el G -> seq_calc G a
| Implies_R G a b
  : seq_calc (a :: G) b ->
    seq_calc G (Implies a b)
| Implies_L G a b c
  : (Implies a b) el G ->
    seq_calc G a ->
    seq_calc (b :: G) c ->
    seq_calc G c.

Hint Constructors seq_calc : core.

(** entailment properties for sequent calculus *)

Lemma seq_calc_reflexivity : Reflexivity seq_calc.
Proof.
  intros G a. revert G. induction a ; eauto 9.
Qed.

Hint Resolve seq_calc_reflexivity : core.

Lemma seq_calc_monotonicity : Monotonicity seq_calc.
Proof.
  intros G G' a H H1.
  revert H.
  revert G'.
  induction H1 ; eauto 10.
Qed.

Theorem weakening : forall G G' a, seq_calc G a -> G <<= G' -> seq_calc G' a.
Proof.
  intros ; eapply seq_calc_monotonicity ; eauto.
Qed.

Lemma seq_calc_cut_lemma :
  forall G a G' b, seq_calc G a -> seq_calc G' b -> seq_calc (G ++ rem G' a) b.
Proof.
  intros G a G' b H.
  revert G G' b H.
  induction a ; intros G G' b D E.
  - 
    remember Falsum as v.
    induction D ; 
      substs ; try congruence ; eauto.
    +
      eapply Implies_L ; eauto using weakening.
  -
    remember (Var v) as tv.
    induction D ; substs ; try inverts Heqtv ; eauto using weakening.
    eapply Implies_L ; eauto using weakening.
  -
    remember (Implies a1 a2) as v.
    induction D ; substs ; try inverts Heqv ; eauto.
    +
      clear IHD.
      induction E as [F | F | F | F] ; auto.
      *
        assert (J : Var a <> Implies a1 a2) by congruence.
        constructor ; auto.
      *
        assert (J : Falsum <> Implies a1 a2) by congruence.
        constructor ; auto.
      *
        apply Implies_R. apply (weakening IHE). auto.
      *
        decide (Implies a b = Implies a1 a2) as [K | K].
        **
          inverts K.
          assert (J : seq_calc (G ++ rem F (Implies a1 a2)) a2)
           by   (apply weakening 
                 with (G := (G ++ rem F (Implies a1 a2)) ++ rem (a1 :: G) a1) ; auto).
          apply weakening
              with (G := (G ++ rem F (Implies a1 a2)) ++
                          rem (G ++ rem (a2 :: F) (Implies a1 a2)) a2) ; auto.
            apply incl_app ; auto. apply rem_app'; auto.
            rewrite rem_comm. auto.
        **
          apply Implies_L with (a := a)(b := b) ; auto.
          eapply (weakening IHE2). auto.
    +
      eapply Implies_L ; eauto. 
      eapply (weakening D1) ; auto.
Qed. 

Theorem admissibility : forall G a b, seq_calc G a -> seq_calc (a :: G) b -> seq_calc G b. 
Proof.
  intros G a b H H'.
  apply weakening with (G := G ++ rem (a :: G) a) ; auto.
  eapply seq_calc_cut_lemma ; eauto.
Qed. 

Lemma seq_calc_no_falsum : ~ seq_calc [] Falsum.
Proof.
  intros H.
  inverts* H.
Qed.

Theorem seq_calc_consistency : Consistency seq_calc.
Proof.
  exists Falsum. apply seq_calc_no_falsum.
Qed. 

Lemma seq_calc_implies : logic_implies seq_calc.
Proof.
  split.
  -
    intros H.
    apply admissibility with (a := Implies a b) ; eauto using weakening.  
  -
    auto.
Qed.

Lemma seq_calc_falsum : logic_falsum seq_calc.
Proof.
  split.
  -
    intros H s. apply admissibility with (a := Falsum) ; auto.
  -
    intros H. apply (H Falsum).
Qed.

Lemma seq_calc_var_empty_ctx v : ~ seq_calc [] (Var v).
Proof.
  intros H.
  inverts H ; crush.
Qed.

