Require Import
        Arith_base
        List
        Tactics.Tactics
        Utils.Basics.


Import ListNotations.


Definition var := nat.


(** syntax for minimal propositional logics *)

Inductive form : Type :=
| Falsum  : form 
| Var     : var -> form
| Implies : form -> form -> form.

Definition not_form f := Implies f Falsum.

Instance form_dec : forall s t : form, dec (s = t).
Proof.
  unfold dec. repeat decide equality.
Qed.

(** some entailment properties *)

Section ENTAILMENT.
  Variable A : Type.
  Variable R : list A -> A -> Prop.

  Definition Reflexivity   := forall G a, a el G -> R G a.
  Definition Monotonicity  := forall G G' a, G <<= G' -> R G a -> R G' a.
  Definition Admissibility := forall G a b, R G a -> R (a :: G) b -> R G a.
  Definition Consistency   := exists a, ~ R nil a. 
End ENTAILMENT.

Definition ctx := list form.

(** some logical properties *)

Definition logic_falsum (R : ctx -> form -> Prop) : Prop :=
  forall G, R G Falsum <-> forall a, R G a.

Definition logic_implies (R : ctx -> form -> Prop) : Prop :=
  forall G a b, R G (Implies a b) <-> R (a :: G) b.
