Require Import
        Program.


Section VECTOR.

  Inductive vector (A : Type) : nat -> Type :=
  | VNil : vector A 0
  | VCons : forall n, A -> vector A n -> vector A (1 + n).

  Arguments VNil {_}.
  Arguments VCons {_}.

End VECTOR.


Variable atom : Set.

Inductive form : nat -> Type :=
| Atom : forall n, atom -> form n
| Implies : forall n, form n -> form (1 + n) -> form (1 + n).

Definition bucket : Type -> Type :=
  fun A => sigT (fun n : nat => vector A n).

Program Fixpoint context (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n' => bucket (form n') * (context n')
  end.
