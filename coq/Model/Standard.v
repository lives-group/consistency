Require Import
        Arith_base
        List
        Program.

Import ListNotations.

(** minimal logic syntax *)

Inductive form : Set :=
| Falsum : form
| Implies : form -> form -> form.

Definition ctx := list form.

(** variables are De Bruijn indexes *)

Inductive var : ctx -> form -> Type :=
| Here : forall G p, var (p :: G) p
| There : forall G p p', var G p -> var (p' :: G) p.

Arguments Here {_}{_}.
Arguments There {_}{_}{_}.


(** natural deduction system *)

Inductive nat_ded : ctx -> form -> Type :=
| Id : forall G p, var G p -> nat_ded G p
| ExFalsum : forall G p, nat_ded G Falsum ->
                    nat_ded G p
| Implies_I : forall G p p',
    nat_ded (p' :: G) p ->
    nat_ded G (Implies p' p)
| Implies_E : forall G p p',
    nat_ded G (Implies p' p) ->
    nat_ded G p' ->
    nat_ded G p.

Arguments Id {_}{_}.
Arguments ExFalsum {_}{_}.
Arguments Implies_I {_}{_}{_}.
Arguments Implies_E {_}{_}{_}.

(** type semantics *)

Program Fixpoint sem_form (p : form) : Type :=
  match p with
  | Falsum => False
  | Implies p1 p2 => sem_form p1 -> sem_form p2
  end.

(** context semantics *)

Program Fixpoint sem_ctx (G : ctx) : Type :=
  match G with
  | [] => unit
  | (t :: G') => sem_form t * sem_ctx G'
  end.


(** variable semantics as context projection *)

Program Fixpoint sem_var {G p}(v : var G p) : sem_ctx G -> sem_form p :=
    match v with
    | Here => fun env => fst env
    | There v' => fun env => sem_var v' (snd env)
    end. 

(** proof semantics *)

Program Fixpoint sem_nat_ded {G p}(H : nat_ded G p) : sem_ctx G -> sem_form p :=
  match H with
  | Id v => fun env => sem_var v env
  | ExFalsum Hf => fun env =>
      match sem_nat_ded Hf env with
      end
  | Implies_I Hp => fun env v' => sem_nat_ded Hp (v' , env)
  | Implies_E Hp Ha => fun env => (sem_nat_ded Hp env) (sem_nat_ded Ha env)
  end. 

(** consistency proof *)

Definition consistency : nat_ded [] Falsum -> False 
  := fun p => sem_nat_ded p tt.
