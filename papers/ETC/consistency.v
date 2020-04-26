(* begin hide *)
Require Import
        Arith_base
        List
        Program.

Import ListNotations.
(* end hide *)


(** printing ctx %$\Gamma$%   *)
(** printing form %$\alpha$%  *)
(** printing [] %$\emptyset$% *)

(**
%\section{Introduction}%

A crucial property of a logical system is consistency, which states that it does not
entails a contradiction%~\cite{}%. Basically, consistency implies that not all formulas
are provable.  While having a simple motivation, consistency proofs rely on
the well-known admissibility of cut property%~\cite{}%, which has a complex inductive proof.
Gentzen, in his seminal work, gives the first consistency proof of logic by introducing an
auxiliar formalism, the sequent calculus, in which consistency is trivial. Next, Gentzen showed
that natural deduction system is equivalent to his sequent calculus extended with an
additional rule: the cut rule. The final (and hardest) piece of Gentzen's proof is to 
show that the cut rule is redundant, i.e., it is admissible. As a consequence, we know
something stronger: all propositions provable in the natural deduction system are also provable
in the sequent calculus without cut. Since we know that the sequent calculus is consistent,
we hence also know that the natural deduction calculus is.

However, proving the admissibility of cut is not an easy task, even for simple logics.
Proofs of admissibility need nested inductions and we need to be really careful to
ensure a decreasing measure on each use of the inductive hypothesis. Such proofs have
a heavy syntactic flavor since they recursively manipulate proof tree structures to
eliminate cuts. A more semantic based approach relies on interpreting logics as its
underlying %$\lambda$%-calculus and prove consistency by using its computation machinery.
In this work, we report the formalization of these two approaches and advocate the use
of the latter since it result on easy to follow proofs. The rest of this work is organized
as follows: Section %\ref{sec:definitions}% present basic definitions about the logic considered
and Section %\ref{sec:semantics}% describe the semantics of our logic objects and its
consistency proofs. Section %\ref{sec:conclusion}% presents a brief comparision between
two consistency proofs and concludes.

%\section{Basic Definitions}\label{sec:definitions}%

In this section we present the main definitions used in our formalization. First, we consider
formulas of a minimal fragment of propositional logics which is formed only by the constant
%\emph{falsum}% (%$\bot$%) and logic implication (%$\supset$%). Following common
practice, we denote contexts by a list of formulas. The following Coq snipetts
declare these concepts.

%\begin{minipage}[c]{0.3\textwidth}%
*)

Inductive form : Set :=
| Falsum : form
| Implies : form -> form -> form.


Definition ctx := list form.

(**
%\end{minipage}%
%\begin{minipage}[c]{0.6\textwidth}%
While types for formulas ([form]) and contexs ([ctx]) have an immediate interpretation, the previous types
miss an important part of propositional logic: variables. We represent variables by an inductive judgement
which states the membership of a formula in a context.
%\end{minipage}%

We let notation %$\alpha \in \Gamma$% denote an inductive predicate that states that a formula %$\alpha$%
is an element of context %$\Gamma$%. The rules for variable judgement and its Coq implementation are presented below.

%\begin{minipage}[c]{0.6\textwidth}%
 *)
Inductive var : ctx -> form -> Type :=
| Here : forall G p, var (p :: G) p
| There : forall G p p', var G p -> var (p' :: G) p.
(**
%\end{minipage}%
%\begin{minipage}[c]{0.3\textwidth}%
%\[%
%\begin{array}{c}%
%\infer[_{\{Here\}}]{\alpha \in (\alpha :: \Gamma)}{}\\ \\%
%\infer[_{\{There\}}]{\alpha \in (\beta :: \Gamma)}{\alpha \in \Gamma} \\ \\%
%\end{array}%
%\]%
%\end{minipage}%
The first constructor of type [var] specifies that a formula %$\alpha$% is in the context %$\alpha :: \Gamma$% and
the constructor [There] specifies that if a formula %$\alpha$% is in %$\Gamma$% then we have
 %$\alpha \in (\beta :: \Gamma)$%, for any formula %$\beta$%.

Using the previous definitions, we can implement natural deduction rules for our minimal logic, as presented below.
*)


(* begin hide *)
Arguments Here {_}{_}.
Arguments There {_}{_}{_}.
(* end hide *)

(**
%\begin{minipage}[c]{0.6\textwidth}%
*)
Inductive nd : ctx -> form -> Type :=
| Id : forall G p,
    var G p ->
    nd G p
| ExFalsum : forall G p,
    nd G Falsum ->
    nd G p
| Implies_I : forall G p p',
    nd (p' :: G) p ->
    nd G (Implies p' p)
| Implies_E : forall G p p',
    nd G (Implies p' p) ->
    nd G p' ->
    nd G p.
(**
%\end{minipage}%
%\begin{minipage}[c]{0.3\textwidth}%
%\[%
%\begin{array}{c}%
%\infer[_{\{Id\}}]{\Gamma \vdash x}{x \in \Gamma} \\ \\%
%\infer[_{\{Ex\}}]{\Gamma \vdash \alpha}{\Gamma \vdash \bot}\\ \\%
%\infer[_{\{\supset-I\}}]{\Gamma \vdash \alpha \supset \beta}{\Gamma \cup \{\alpha\} \vdash \beta}\\ \\%
%\infer[_{\{\supset-E\}}]{\Gamma \vdash \beta}{\Gamma \vdash \alpha \supset \beta & \Gamma \vdash \alpha}%
%\end{array}%
%\]%
%\end{minipage}%

The first rule ([Id]) stabilishes that any formula in the context is provable and rule [ExFalsum] defines
the principle %\emph{ex-falsum quod libet}% which allow us to prove any formula if we have a deduction of [Falsum].
Rule [Implies_I] specifies that from a deduction of a formula [p] from a context [p' :: G], [nd (p' :: G) p],
we can prove the implication [Implies p' p]. The last rule, [Implies_E], represents the well-known %\emph{modus-ponens}%,
which allows us to deduce a formula [p] from deductions of [Implies p' p] and [p'].

Next section uses the relation between logics and %$\lambda$%-calculus and its evaluation to prove the consistency of
minimal logic.
*)


(* begin hide *)
Arguments Id {_}{_}.
Arguments ExFalsum {_}{_}.
Arguments Implies_I {_}{_}{_}.
Arguments Implies_E {_}{_}{_}.
(* end hide *)

(**
 %\section{Semantics and Consistency}\label{sec:semantics}%

We prove the consistency of logics by exploring its correspondence with the simply typed
%$\lambda$%-calculus %~\cite{}%. The Curry-Howard correspondence is a crucial idea in modern
logics that shows the similarity of logical formalisms and its computational counterparts.

FINISH INTRODUCTORY TEXT

We define the denotation of a formula by recursion on its structure. The idea is to associate the
empty type ([False]) with the formula [Falsum] and a function type with formula [Implies p1 p2],
as presented next.
 *)

Program Fixpoint sem_form (p : form) : Type :=
  match p with
  | Falsum => False
  | Implies p1 p2 => sem_form p1 -> sem_form p2
  end.

(**
Using [sem_form] function, we can define context semantics as tuples
of formula semantics as follows:
 *)

Program Fixpoint sem_ctx (G : ctx) : Type :=
  match G with
  | [] => unit
  | (t :: G') => sem_form t * sem_ctx G'
  end.
(**
Function [sem_ctx] recurses over the structure of the input context building
right-nested tuple ending with the Coq [unit] type, which is a type with a
unique element. Since context are mapped intro tuples, variables must be
mapped into projections on such tuples. This would allow us to retrieve the
value associated with a variable in a context.
*)

Program Fixpoint sem_var {G p}(v : var G p) : sem_ctx G -> sem_form p :=
    match v with
    | Here => fun env => fst env
    | There v' => fun env => sem_var v' (snd env)
    end. 

(**
Function [sem_var] receives a variable (value of type [var G p]) and a semantics
of a context (a value of type [sem_ctx G]) and returns the value of the formula
represented by such variable. Whenever the variable is built using constructor [Here],
we just return the first component of the input context semantics and when we have
the constructor [There] we just call  [sem_var] recursively.

Our next step is to define the semantics of natural deduction proofs. The semantics of
proofs is implemented by function [sem_nat_ded] which maps proofs (values of type [nat_ded G p])
and context semantics (values of type [sem_ctx G]) to the value of input proof conclusion
(type [sem_form p]). The first case specifies that the semantics of an identity rule proof
(constructor [Id]) is just retrieving the value of the underlying variable in the context semantics
by calling function [sem_var]. Second case deals with [ExFalsum] rule: we recurse over the proof
object [Hf] which will produces a Coq object of type [False], which is empty and so we can finish the
definition with an empty pattern match. Semantics of implication introduction ([Implies_I]) simply
recurses on the subderivation [Hp] using an extended context [(v' , env)]. Finally, we define the
semantics of implication elimination as simply function application of the results of the
recursive call on its two subderivations.
*)

Program Fixpoint sem_nat_ded {G p}(H : nat_ded G p)
  : sem_ctx G -> sem_form p :=
  match H with
  | Id v => fun env => sem_var v env
  | ExFalsum Hf => fun env =>
      match sem_nat_ded Hf env with
      end
  | Implies_I Hp => fun env v' => sem_nat_ded Hp (v' , env)
  | Implies_E Hp Ha => fun env => (sem_nat_ded Hp env) (sem_nat_ded Ha env)
  end. 

(**
Using all thoses previously defined pieces we can prove the consistency of our little natural
deduction system merely by showing that it should not be the case that we have a proof of [Falsum]
using the empty set of assumptions. We can proof such fact by exhbiting a term of type
[nat_ded [] Falsum -> False]%\footnote{Here we use the fact that $\neg \alpha$ is
equivalent to $\alpha \supset \bot$.}%, which is trivially done by using function [sem_nat_ded].
 *)

Theorem consistency : nat_ded [] Falsum -> False := fun p => sem_nat_ded p tt.


(**
%\section{Conclusion}\label{sec:conclusion}%
 *)
