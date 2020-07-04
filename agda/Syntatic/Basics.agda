module Basics where

infix  4 _∋_
infixl 5 _,_
infixr 6 _⇒_
infixr 7 _∧_
infixr 7 _∨_
infixl 3 _+_

-- Defining natural numbers.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- Defining the sum of two natural numbers.
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

-- Syntax for formulae.
data Form : Set where
  ⊤   : Form
  _⇒_  : Form → Form → Form
  _∧_ : Form → Form → Form
  _∨_ : Form → Form → Form
  ⊥   : Form

-- Defining the size of a formula.
formula-size : Form → ℕ
formula-size ⊤ = zero
formula-size (D ⇒ D₁) = (suc zero) + (formula-size D) + (formula-size D₁)
formula-size (D ∧ D₁) = (suc zero) +(formula-size D) + (formula-size D₁)
formula-size (D ∨ D₁) = (suc zero) + (formula-size D) + (formula-size D₁)
formula-size ⊥ = zero

-- Defining context.
data Context : Set where
  ∅   : Context
  _,_  : Context → Form → Context

-- Defining the size of a context of formulae.
context-size : Context → ℕ
context-size ∅ = zero
context-size (G , x) = (context-size G) + (formula-size x)

-- Context membership proofs.
data _∋_ : Context → Form → Set where
  Z : ∀ {Γ A}    → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

-- Defining the type Maybe.
data Maybe (a : Set) : Set where
  nothing : Maybe a
  just    : a → Maybe a

maybe : {A B : Set} → (A → B) → B → Maybe A → B
maybe _ v nothing = v
maybe f _ (just x) = f x

-- Defining disjuction in the meta language.
data _⊎_ (A B : Set) : Set where
  inls : A → A ⊎ B
  inrs : B → A ⊎ B

-- Defining false in the meta language.
data bottom : Set where

-- Defining a contradiction in the meta language.
bottom-elim : ∀ {A : Set} → bottom → A
bottom-elim ()

-- Defining the negation of a sentence in the meta language.
¬_ : Set → Set
¬ A = A → bottom
