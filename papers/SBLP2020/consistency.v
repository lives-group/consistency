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
(** printing nat %$\mathbb{N}$% *)
(** printing el %$\in$% *)

(**
%\section{Introduction}%

A crucial property of a logical system is consistency, which states that it does not
entails a contradiction. Basically, consistency implies that not all formulas
are provable.  While having a simple motivation, consistency proofs rely on
the well-known admissibility of cut property, which has a rather delicate inductive proof.
Gentzen, in his seminal work%~\cite{Gentzen36}%, gives the first consistency proof of logic by introducing an
auxiliary formalism, the sequent calculus, in which consistency is trivial. Next, Gentzen showed
that the natural deduction system is equivalent to his sequent calculus extended with an
additional rule: the cut rule. The final (and hardest) piece of Gentzen's proof is to 
show that the cut rule is redundant, i.e., it is admissible. As a consequence, we know
something stronger: all propositions provable in the natural deduction system are also provable
in the sequent calculus without cut. Since we know that the sequent calculus is consistent,
we hence also know that the natural deduction calculus is%~\cite{Negri2001}%.

However, proving the admissibility of cut is not easy, even for simple logics.
Proofs of admissibility need nested inductions, and we need to be really careful to
ensure a decreasing measure on each use of the inductive hypothesis. Such proofs have
a heavy syntactic flavor since they recursively manipulate proof tree structures to
eliminate cuts. A more semantics-based approach relies on interpreting logics as its
underlying %$\lambda$%-calculus and proves consistency by using its computation machinery.
In this work, we report on formalizing these two approachs for a minimal version of
propositional logics.

This work results from a research project motivated by questions raised by
undergraduate students on a first course on formal logics at Universidade Federal de Ouro Preto.
The students were encouraged to "find the answer" by formalizing it in proof assistant systems.
After some months following basic exercices on Agda and Coq on-line text books%~\cite{plfa2019,Pierce18}%,
they were able to start the formalization of consistency for propositional logics. This work reports on
the Coq formalization of two different approaches for consistency proofs for a minimal version of
propositional logics and briefly discuss an Agda formalization of the same results also considering
the conjunction and disjunction connectives. We are aware that more extensive formalizations of propositional logic already
exists in Coq%~\cite{doorn2015}% and other proof assistants%~\cite{Nipkow17}%. However, our focus is
on showing how a better understanding of the Curry-Howard correspondence can lead to simple formalizations
of mathematical results through its computational representation.


More specifically, we contribute:

%\begin{itemize}%
   %\item We present a semantics-based consistency proof for minimal propositional logic in Coq.%
   %Our proof is completely represented as Coq functions using dependently-typed pattern maching%
   %in less than 90 lines of code.%
   %\item We also formalize the traditional proof theoretical cut-based proof of consistency. Unlike the semantics-based%
   %proof, this formalization required the definition of several intermediate definitions and lemmas to complete the proof.%
   %Instead of focusing on presenting tactic scripts, we outline the proof strategies used in the main lemmas used to ensure%
   %the consistency.%
   %\item We formalize the same results in the context of a broader version of propositional logics in Agda
   programming language and present some conclusions obtained by coding these results in a different proof assistant.%
%\end{itemize}%

We organize this work as follows: Section %\ref{sec:definitions}% presents basic definitions
about the logic considered and Section%~\ref{sec:coq}% presents a brief introduction to the Coq proof assistant.
Section %\ref{sec:semantics}% describes the semantics-based proof of consistency
implemented in  Coq and Section %\ref{sec:admissibility}% presents our formalization of Gentzen's style consistency proof.
We briefly discuss our Agda formalization in Section%~\ref{sec:agda}%.
Section %\ref{sec:lessons}% draws some lessons learned during the formalization of these consistency proofs.
Finally, Section %\ref{sec:related}% presents related works and Section %\ref{sec:conclusion}% concludes.

The complete formalization was verified using Coq version 8.10.2 and it is available
on-line%~\cite{Sasdelli20}% together with the %\LaTeX~% files needed to build this work.

%\section{Basic Definitions}\label{sec:definitions}%

In this work, we consider a fragment of propositional logic which is formed by the constant
%\emph{falsum}% (%$\bot$%), logic implication (%$\supset$%) and variables (represented by meta-variable %$v$%), as
described by the following context free grammar:
%
\[\alpha ::= \bot \,\mid\,v\,\mid\,\alpha\,\supset\,\alpha\]
%

Following common practice, we let meta-variable %$\Gamma$% denote contexts by a list of formulas where %$\emptyset$% denotes
the empty context and %$\Gamma \cup \{\alpha\}$% includes the formula %$\alpha$% in %$\Gamma$%. Using contexts, we
can define natural deduction as an inductively defined judgment %$\Gamma \vdash \alpha$% which denotes that the
formula %$\alpha$% can be deduced from the hypothesis present in %$\Gamma$% using the following rules:

%\[%
%\begin{array}{cc}%
%\infer[_{\{Id\}}]{\Gamma \vdash \alpha}{\alpha \in \Gamma} &%
%\infer[_{\{Ex\}}]{\Gamma \vdash \alpha}{\Gamma \vdash \bot}\\ \\%
%\infer[_{\{\supset-I\}}]{\Gamma \vdash \alpha \supset \beta}{\Gamma \cup \{\alpha\} \vdash \beta} &%
%\infer[_{\{\supset-E\}}]{\Gamma \vdash \beta}{\Gamma \vdash \alpha \supset \beta & \Gamma \vdash \alpha}%
%\end{array}%
%\]%

Rule %$Id$% shows that any hypothesis in %$\Gamma$% is provable and rule %$Ex$% which specifies that from a
contradiction we can deduce any formula. The rule %$\supset-I$% shows that we can deduce %$\alpha\supset \beta$%
if we are able to prove %$\beta$% from %$\Gamma\cup\{\alpha\}$% and rule %$\supset-E$% is the well-known
%\emph{modus ponens}% rule.

We let notation %$\Gamma\Rightarrow\alpha$% denote that %$\alpha$% is deducible from the hypothesis in %$\Gamma$%
using the rules of the sequent calculus which are presented next. The only difference with the natural deduction
is in one rule for implication. The sequent calculus rule counter-part for implication elimination is called
implication left rule, and it states that we can conclude any formula %$\gamma$% in a context %$\Gamma$% if we have
that: 1) %$\alpha \supset \beta \in \Gamma$%; 2) %$\Gamma \Rightarrow \alpha$% and 3) %$\Gamma \cup \{\beta\} \Rightarrow \gamma$%.
%
\[
\begin{array}{cc}
\infer[_{\{Id\}}]{\Gamma \Rightarrow \alpha}{\alpha \in \Gamma} &
\infer[_{\{Ex\}}]{\Gamma \Rightarrow \alpha}{\Gamma \Rightarrow \bot}\\ \\
\multicolumn{2}{c}{\infer[_{\{\supset-R\}}]{\Gamma \Rightarrow \alpha \supset \beta}{\Gamma \cup \{\alpha\} \Rightarrow \beta}} \\ \\
\multicolumn{2}{c}{\infer[_{\{\supset-L\}}]{\Gamma \Rightarrow \gamma}{
                                                       \alpha \supset \beta \in
                                                        \Gamma &
                                                        \Gamma \Rightarrow
                                                        \alpha & \Gamma \cup
                                                        \{\beta\}\vdash \gamma}}
\end{array}
\]
%
We say that the natural deduction system is consistent if there is no proof of %$\emptyset\vdash \bot$%. The same idea applies to sequent calculus.
In the next section, we describe our Coq formalization of the consistency for natural deduction using a semantics-based approach.

%\section{A Taste of Coq Proof Assistant}\label{sec:coq}%

Coq is a proof assistant based on the calculus of inductive
constructions (CIC)%~\cite{Bertot04}%, a higher order typed
$\lambda$-calculus extended with inductive definitions.  Theorem
proving in Coq follows the ideas of the so-called
``BHK-correspondence''%\footnote{Abbreviation of Brouwer, Heyting,
  Kolmogorov, de Bruijn and Martin-L\"of Correspondence. This is also
  known as the Curry-Howard ``isomorphism''.}%, where types represent
logical formulas, %$\lambda$%-terms represent proofs
%~\cite{Sorensen06}% and the task of checking if a piece of text is a
proof of a given formula corresponds to checking if the term that
represents the proof has the type corresponding to the given formula.

However, writing a proof term whose type is that of a logical formula
can be a hard task, even for very simple propositions.  In order to
make the writing of complex proofs easier, Coq provides
%\emph{tactics}%, which are commands that can be used to construct proof
terms in a more user friendly way.

As a tiny example, consider the task of proving the following simple
formula of propositional logic:
%
\[
(A \to B)\to (B\to C) \to A \to C
\]
%
In Coq, such theorem can be expressed as:
 *)

Section EXAMPLE.
   Variables A B C : Prop.
   Theorem example : (A -> B) -> (B -> C) -> A -> C.
   Proof.
       intros H H' HA. apply H'. apply H. assumption. 
   Qed.
End EXAMPLE.

(**
In the previous source code piece, we have defined a Coq section named
[EXAMPLE]%\footnote{In Coq, we can use sections to delimit the
  scope of local variables.}% which declares variables [A],
[B] and [C] as being propositions (i.e. with type
[Prop]). Tactic [intros] introduces variables
[H], [H'] and [HA] into the (typing) context,
respectively with types [A -> B], [B -> C] and
[A] and leaves goal [C] to be proved. Tactic
[apply], used with a term [t], generates goal [P]
when there exists [t: P -> Q] in the typing context and the
current goal is [Q]. Thus, [apply H'] changes the goal
from [C] to [B] and [apply H] changes the goal to
[A]. Tactic [assumption] traverses the typing context to
find a hypothesis that matches with the goal.

We define next a proof of the previous propositional logical formula
that, in contrast to the previous proof, that was built using tactics
([intros], [apply] and [assumption]), is coded
directly as a function:
 *)

Definition example'
  : (A -> B) -> (B -> C) -> A -> C :=
   fun (H : A -> B) (H' : B -> C) (HA : A) => H' (H HA).

(**
However, even for very simple theorems, coding a definition directly
as a Coq term can be a hard task. Because of this, the use of tactics
has become the standard way of proving theorems in Coq. Furthermore,
the Coq proof assistant provides not only a great number of tactics
but also have a domain specific language for scripted proof automation,
called %$\mathcal{L}$tac%. More information about Coq and  %$\mathcal{L}$tac% can be found
in%~\cite{Chlipala13,Bertot04}%.


%\section{Semantics-based proof}\label{sec:semantics}%

Our first task in formalizing the consistency is how to represent formulas (type [form]), which
are represented by the false constant ([Falsum] constructor) and implication ([Implies] constructor).
Contexts are just a list of formulas.
*)

Inductive form : Set :=
| Falsum : form
| Implies : form -> form -> form.


Definition ctx := list form.

(**
In order to represent variables, We follow a traditional approach in programming languages community
and use %\emph{De Bruijn indexes}~\cite{DeBruijn71}% represented as an inductive judgement between
formulas and contexts:
%\[%
%\begin{array}{cc}%
%\infer[_{\{Here\}}]{\alpha \in (\alpha :: \Gamma)}{} &%
%\infer[_{\{There\}}]{\alpha \in (\beta :: \Gamma)}{\alpha \in \Gamma}%
%\end{array}%
%\]%
In essence, this judgment states the membership of a formula %$\alpha$% in a context %$\Gamma$%. 
The Coq encoding of this predicate is straightforward.
 *)

Inductive var : ctx -> form -> Type :=
| Here : forall G p, var (p :: G) p
| There : forall G p p', var G p -> var (p' :: G) p.

(**
The first constructor of type [var] specifies that a formula %$\alpha$% is in the context %$\alpha :: \Gamma$% and
the constructor [There] specifies that if a formula %$\alpha$% is in %$\Gamma$%, then we have
 %$\alpha \in (\beta :: \Gamma)$%, for any formula %$\beta$%.

Using the previous definitions, we can implement natural deduction rules for our minimal logic, as presented below.
*)


(* begin hide *)
Arguments Here {_}{_}.
Arguments There {_}{_}{_}.
(* end hide *)

Inductive nd : ctx -> form -> Type :=
| Id : forall G p, var G p -> nd G p
| ExFalsum : forall G p, nd G Falsum -> nd G p
| Implies_I : forall G p p', nd (p' :: G) p -> nd G (Implies p' p)
| Implies_E : forall G p p', nd G (Implies p' p) -> nd G p' -> nd G p.

(**
The first rule ([Id]) estabilishes that any formula in the context is provable and rule [ExFalsum] defines
the principle %\emph{ex-falso quodlibet}%, which allows us to prove any formula if we have a deduction of [Falsum].
Rule [Implies_I] specifies that from a deduction of a formula [p] from a context [p' :: G], [nd (p' :: G) p],
we can prove the implication [Implies p' p]. The last rule, [Implies_E], represents the well-known %\emph{modus-ponens}%,
which allows us to deduce a formula [p] from deductions of [Implies p' p] and [p'].

The Curry-Howard isomorphism states that there is a correspondence between logics and functional programming by
relating logical formulas to types and proofs to %$\lambda$%-calculus terms %\cite{Sorensen06}%. In order to prove
consistency of natural deduction system, we use this analogy with %$\lambda$%-calculus. Basically, under the
Curry-Howard interpretation, saying that there is no proof for %$\emptyset \vdash \bot$%
(the statement of the consistency property) resorts to show that there is no value%\footnote{A value is a well-typed term
which can not be further reduced according to a semantics.}% of type %$\bot$%. A way to ensure that a type
has no value, is to reduce arbitrary terms until we no more reductions steps apply and that is the strategy of our
semantics-based proof: build an algorithm to reduce proof terms and use it to show that there are no proofs
for %$\bot$%.

The reduction algorithm we use is an well-typed interpreter for the simply-typed %$\lambda$%-calculus based on a
standard model construction. The first step in the implementation is to define the denotation of a formula by
recursion on its structure. The idea is to associate the empty type ([False]) with the formula [Falsum] and a
function type with formula [Implies p1 p2], as presented next.
 *)

(* begin hide *)
Arguments Id {_}{_}.
Arguments ExFalsum {_}{_}.
Arguments Implies_I {_}{_}{_}.
Arguments Implies_E {_}{_}{_}.
(* end hide *)

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
unique element. Since contexts are mapped intro tuples, variables must be
mapped into projections on such tuples. This would allow us to retrieve the
value associated with a variable in a context.
*)

Program Fixpoint sem_var {G p}(v : var G p)
  : sem_ctx G -> sem_form p :=
    match v with
    | Here => fun env => fst env
    | There v' => fun env => sem_var v' (snd env)
    end. 

(**
Function [sem_var] receives a variable (value of type [var G p]) and a semantics
of a context (a value of type [sem_ctx G]) and returns the value of the formula
represented by such variable. Whenever the variable is built using constructor [Here],
we just return the first component of the input context semantics, and when we have
the constructor [There], we just call [sem_var] recursively.

Our next step is to define the semantics of natural deduction proofs. The semantics of
proofs is done by function [sem_nat_ded], which maps proofs (values of type [nat_ded G p])
and context semantics (values of type [sem_ctx G]) to the value of input proof conclusion
(type [sem_form p]). The first case specifies that the semantics of an identity rule proof
(constructor [Id]) is just retrieving the value of the underlying variable in the context semantics
by calling function [sem_var]. The second case deals with [ExFalsum] rule: we recurse over the proof
object [Hf] which will produce a Coq object of type [False], which is empty and so we can finish the
definition with an empty pattern match. Semantics of implication introduction ([Implies_I]) simply
recurses on the subderivation [Hp] using an extended context [(v' , env)]. Finally, we define the
semantics of implication elimination as simply function application of the results of the
recursive call on its two subderivations.
*)

Program Fixpoint sem_nat_ded {G p}(H : nat_ded G p)
  : sem_ctx G -> sem_form p :=
  match H with
  | Id v => fun env =>  sem_var v env
  | ExFalsum Hf => fun env =>
      match sem_nat_ded Hf env with end
  | Implies_I Hp => fun env v' => sem_nat_ded Hp (v' , env)
  | Implies_E Hp Ha => fun env =>
      (sem_nat_ded Hp env) (sem_nat_ded Ha env)
  end. 

(**
Using all those previously defined pieces, we can prove the consistency of our little natural
deduction system merely by showing that it should not be the case that we have a proof of [Falsum]
using the empty set of assumptions. We can prove such fact by exhibiting a term of type
[nat_ded [] Falsum -> False]%\footnote{Here we use the fact that $\neg \alpha$ is
equivalent to $\alpha \supset \bot$.}%, which is trivially done by using function [sem_nat_ded] with term
[tt], which is the value of type [unit] that denotes the semantics of the empty context needed to call
[sem_nat_ded].
 *)

Theorem consistency : nat_ded [] Falsum -> False
  := fun p => sem_nat_ded p tt.

(**
%\section{Gentzen style proof}\label{sec:admissibility}%

Now, we turn our attention to formalizing the admissibility of cut based consistency proof in Coq.
Unlike our semantics-based proof, which uses dependently typed syntax to concisely represent formulas and
natural deduction proofs, we use an explicity approach in representing formulas as sequent calculus proofs.
We use natural numbers to represent variables and formulas are encoded as simple inductive type which has
an immediate meaning.
 *)

Definition var := nat.

Inductive form : Type :=
| Falsum  : form 
| Var     : var -> form
| Implies : form -> form -> form.

(**
The main change on how we represent the sequent calculus is in the
rule for variables. We use the Coq library boolean list membership predicate
[member], which fits better for proof automation. In order to
simplify the task of writing code that uses this predicate, we defined
notation [a el G] which means [member a G]. 

Next, we the sequent calculus formulation for our minimal logic. The only
difference with the natural deduction is in one rule for implication. The
sequent calculus rule counter-part for implication elimination is called
implication left rule, which states that we can conclude any formula $\gamma$
in a context $\Gamma$ if we have that: 1) $\alpha \supset \beta \in \Gamma$;
2) $\Gamma \Rightarrow \alpha$ and 3) $\Gamma \cup \{\beta\} \Rightarrow
\gamma$. The rules for the sequent-calculus and its correspondent Coq
implementation are presented next.
 *)

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

(**
An important property of sequent calculus derivations is the weakening which
states that it stable under the inclusion of new hypothesis.
%
\begin{Lemma}[Weakening]\label{lemma:weak}
If %$\Gamma \subseteq \Gamma'$% and %$\Gamma\Rightarrow \alpha$% then %$\Gamma'\Rightarrow \alpha$%.
\end{Lemma}
\begin{proof}
  Induction on the derivation of $\Gamma\Rightarrow\alpha$.
\end{proof}
%
Since weakening has a straightforward inductive proof (coded as 4 lines tactic script),
we do not comment on its details. However, this proof is used in several points in the admissibility
of cut property, which we generalize using the following lemma in order to get a stronger induction hypothesis.

%
\begin{Lemma}[Generalized admissibility]\label{lemma:admissibility}
   If $\Gamma\Rightarrow\alpha$ and $\Gamma'\Rightarrow \beta$ then $\Gamma \cup (\Gamma' - \{\alpha\}) \Rightarrow \beta$.
\end{Lemma}
\begin{proof}
   The proof proceeds by induction on the structure of the cut formula $\alpha$. The cases for $\alpha = \bot$ and
   $\alpha$ is a variable easily follows by induction on  $\Gamma\Rightarrow\alpha$ and using weakening on the variable case.
   The interesting case is when $\alpha = \alpha_1 \supset \alpha_2$ in which we proceed by induction on $\Gamma\Rightarrow\alpha$.
   Again, most of cases are straightforward except when the last rule used to conclude $\alpha_1\supset\alpha_2$ was $\supset-R$.
   In this situation, we proceed by induction on $\Gamma'\Rightarrow \beta$. The only interesting cases are when the last rule was
   $\supset-L$ or $\supset-R$. If the last rule used in deriving $\Gamma' \Rightarrow \beta$ was
   $\supset-R$ we have: $\beta = a \supset b$, for some $a,b$.
   Also, we have that $\Gamma' \cup \{a\}\Rightarrow b$. By the
   induction hypothesis on $\Gamma' \cup \{a\}\Rightarrow b$, we
   have that $\Gamma \cup ((\Gamma' \cup \{a\}) - \{\alpha_1 \supset \alpha_2\})\Rightarrow b$. Since we have 
   $\Gamma \cup ((\Gamma' \cup \{a\}) - \{\alpha_1 \supset \alpha_2\})\Rightarrow b$ then we also have
   $\Gamma \cup (\Gamma' \cup \{a\} - \{\alpha_1 \supset \alpha_2\}) \cup \{a\} \Rightarrow b$ and conclusion follows by rule
   $\supset-R$. The case for $\supset-L$ follows the same structure.
\end{proof}
%
Using the previous defined lemma, the admissibility of cut is an immediate corollary.

%
\begin{Corollary}[Admissibility of cut]
  If $\Gamma \Rightarrow \alpha$ and $\Gamma \cup\{\alpha\}\Rightarrow \beta$
  then $\Gamma \Rightarrow \beta$.
\end{Corollary}
\begin{proof}
  Immediate consequence of Lemmas~\ref{lemma:weak} and~\ref{lemma:admissibility}.
\end{proof}
%

Consistency of sequent calculus trivially follows by inspection on the structure of
derivations.
%
\begin{Theorem}[Consistency of sequent calculus]\label{theorem:consistency}
  There is no proof of $\emptyset \Rightarrow \bot$.
\end{Theorem}
\begin{proof}
  Immediate from the sequent calculus rules (there is no rule to introduce $\bot$).
\end{proof}
%

The next step in the mechanization of the
consistency of our minimal logic is to stabilish the equivalence between sequent
calculus and natural deduction systems. The equivalence proofs between these two
formalism are based on a routine induction on derivations using admissibility of
cut. We omit its description for brevity. The complete proofs of these
equivalence results can be found in our code repository%~\cite{Sasdelli20}%. 
Finally, we can prove the consistency of natural deduction by combining the
proofs of consistency of the sequent calculus and the equivalence between these
formalisms.
%
\begin{Theorem}[Consistency for Natural Deduction]
  There is no proof of $\emptyset \vdash \bot$.
\end{Theorem}
\begin{proof}
  Suppose that $\emptyset \vdash \bot$. By the equivalence between natural
  deduction and sequent calculus, we have $\emptyset\Rightarrow \bot$, which
  contradicts Theorem~\ref{theorem:consistency}.
\end{proof}  
%

%\section{Agda formalization}\label{sec:agda}%

In this section we briefly present some details of our Agda formalization
of consistency proofs for propositional logics. Since the Agda version of the
consistency proof using a well-typed interpreter for the simply-typed
%$\lambda$%-calculus is essentially the same as our Coq implementation, we will focus
on the admissibility of cut version.

One important design decision of our Agda proof was how to represent a permutation
relation between contexts. In our Coq code we simply "lift" the boolean list membership test to
set equality relation and use facilities offered by small-scale reflection and type classes
to ease evidence construction%~\cite{GonthierM10,GonthierZND11}%.

%\section{Lessons learned}\label{sec:lessons}%

Previous sections presented two different formalizations for consistency of minimal
propositional logic in Coq proof assistant. In this section, we briefly resume the
main characteristics of each approach and try to draw some conclusions on the
realized proof effort.

The first strategy is inspired by the Curry-Howard correspondence and it is,
in essence, a well-typed interpreter for the
simply-typed %$\lambda$%-calculus. The consistency is ensured by construct a term
that asserts that is impossible to build a term of type [Falsum] from an empty
context, which is done by a simple call to the %$\lambda$%-calculus interpreter.
The complete formalization is 85 lines long and we only use the [Program] construct
which eases the task of dependently-typed pattern matching, which is necessary
to construct functions which manipulate richly typed structures like type [var] or
build types from values like [sem_form] and [sem_ctx]. No standard tactic or
tatic library is used to finish the formalization.

The second strategy implements the usual proof theoretical approach to guarantee
the consistency of logics. As briefly described in the previous section, proving
the admissibility of cut needs nested inductions on the structure of the cut-formula
and on the structure of the sequent-calculus derivations. The main problem on proving
the cut lemma is the bureocratic adjustement of contexts by using weakening in the
right places in the proof. Our proof uses some tactics libraries%~\cite{Chlipala13, Pierce18}%
and type class based automation to automatically produce proof terms for subset relation
between contexts. Our cut-based consistency proof has around 270 lines of code without
considering the tactics libraries used. 

When comparing the both approachs, it is obvious that the second demands approximately
3 times more lines of code than the first. However, while demanding more code,
the cut-based proof essentially follows the ideas used in proof-theory textbooks.
One of main difficulties in formalizing the Gentzen style proof was the correct handling of
weakening. The usage of proof automation tools and Coq type classes had a great impact
on the simplification of these results.
The semantics-based proof rely on the relation between the minimal propositional logic and
the simply-typed %$\lambda$%-calculus, i.e., it is necessary to understand the consequences
of the Curry-Howard isomorphism.

%\section{Related work}\label{sec:related}%

%\paragraph{Formalizations of logics}Proof assistants has been used with sucess to formalize
several logical theories. van Doorn describes a formalization of some important results about
propositional logic in Coq: completeness of natural deduction, equivalence between natural
deduction and sequent calculus and the admissibility of cut theorem~\cite{doorn2015}. In his formalization,
van Doorn considered the full syntax of propositional logic (including negation, disjuntion and conjunction) and
also have proved completeness of natural deduction. In our work, we tried to keep things to a bare minimum by
considering a minimalistic version of propositional logic. We intend to include the missing conectives as
future work. Another formalization of propositional logic was implemented by Michaelis and Nipkow~\cite{Nipkow17} which
covered several proof systems (sequent calculus, natural deduction, Hilbert systems, resolution) and proved the some
important meta-theoretic results like: compactness, translations between proof systems, cut-elimination and model existence.

A formalization of linear logic was conducted by Allais and McBride~\cite{allais18}. In essence, Allais and McBride work
starts from a well-scoped $\lambda$-calculus and introduce a typed representation which leads to a intuitionistic version
of linear logic which uses a relation that ensure the resource control behavior of linear logic proofs. Another work which
formalizes linear logic was developed by Xavier et. al~\cite{xavier18}. The main novelty of their work was the formalization
of a focused linear logic using a binding representation called parametric high-order abstract syntax (PHOAS)~\cite{Chlipala08}.

\paragraph{Applications of proof assistants.}

Ribeiro and Du Bois~\cite{Ribeiro2017} described the formalization of a RE
(regular expression) parsing algorithm that produces a bit representation
of its parse tree in the dependently typed language Agda. The algorithm computes bit-codes using Brzozowski derivatives and
they proved that the produced codes are equivalent to parse trees ensuring soundness and completeness with respect to an
inductive RE semantics. They included the certified algorithm in a tool developed by themselves, named verigrep, for RE-based
search in the style of GNU grep. While the authors provided formal proofs, their tool show a bad performance when compared to
other approaches to RE parsing.

A formal constructive theory of RLs (regular language) was presented by Doczkal et. al. in
\cite{Doczkal2013}. They formalized some fundamental results about RLs.
For their formalization, they used the Ssreflect extension to Coq, which
features an extensive library with support for reasoning about finite
structures such as finite types and finite graphs. They established all
of their results in about 1400 lines of Coq, half of which are specifications.
Most of their formalization deals with translations between different
representations of RLs, including REs, DFAs (deterministic finite automata),
minimal DFAs and NFAs (non-deterministic finite automata).
They formalized all these (and other) representations and constructed
computable conversions between them. Besides other interesting aspects
of their work, they proved the decidability of language equivalence
for all representations. Unlike our work, Doczkal et. al.'s only concerns
about formalizing classical results of RL theory in Coq, without using the
formalized automata in practical applications, like matching or parsing.
%


%\section{Conclusion}\label{sec:conclusion}%

In this work we briefly describe a Coq formalization of a semantics based consistency proof for
minimal propositional logic. The complete proof is only 85 lines long and only use of some basic
dependently typed programming features of Coq. We also
formalize the consistency of this simple logic in Coq using Gentzen's admissibility of cut approach
which resulted in longer formalization: the formalization has around 270 lines of code, which were much
simplified by using some tactics libraries.

As future work, we intend to extend the current formalization to full propositional logic and also
other formalisms like Hilbert systems and analytic tableaux%~\cite{smullyan1995first}%.
 *)
