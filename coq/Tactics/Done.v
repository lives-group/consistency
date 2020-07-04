(** simple tactic to mimic SSreflects done *)

Require Import
        Omega
        Tactics.Crush.

Ltac done :=
  trivial; intros; solve
  [ repeat first
    [ solve [trivial]
    | solve [symmetry; trivial]
    | reflexivity
    | try omega ; crush
    | discriminate
    | contradiction
    | split ]
  | match goal with H : ~_ |- _ => solve [destruct H; trivial] end ].


Tactic Notation "by" tactic(tac) :=
  tac; done.