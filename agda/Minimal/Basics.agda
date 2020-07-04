module Basics where

-- propositional equality

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

sym : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a}{A : Set a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {a}{A B : Set a}{x y : A}(f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {a b}{A : Set a}{x y : A}(P : A → Set b) → x ≡ y → P x → P y
subst P refl px = px

-- inspect idiom

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

-- equational reasoning

infix  1 begin-≡_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  3 _≡-∎

begin-≡_ : ∀ {a}{A : Set a}{x y : A} → x ≡ y → x ≡ y
begin-≡_ x≡y  =  x≡y

_≡⟨⟩_ : ∀ {a}{A : Set a}(x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y  =  x≡y

_≡⟨_⟩_ : ∀ {a}{A : Set a}(x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

_≡-∎ : ∀ {a}{A : Set a}(x : A) → x ≡ x
x ≡-∎  =  refl

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

infixr 3 _⊎_

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

[_,_] : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
[ f , g ] (inl x) = f x
[ f , g ] (inr x) = g x

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 9 _∘_

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

¬_ : Set → Set
¬ A = A → ⊥

_≢_ : ∀ {a}{A : Set a} → A → A → Set a
x ≢ y = x ≡ y → ⊥

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

dec : ∀ {P A : Set} → (P → A) → (¬ P → A) → Dec P → A
dec P ¬P (yes p) = P p
dec P ¬P (no ¬p) = ¬P ¬p

id : ∀ {l}{A : Set l} → A → A
id x = x

infix 0 _↔_

record _↔_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A

-- bijections form an equivalence relation

↔-refl : ∀ {A} → A ↔ A
↔-refl
  = record {
      to = id
    ; from = id }

↔-sym : ∀ {A B} → A ↔ B → B ↔ A
↔-sym r
   = record {
     to = _↔_.from r
   ; from = _↔_.to r }

↔-trans : ∀ {A B C} → A ↔ B → B ↔ C → A ↔ C
↔-trans r r'
  = record {
      to = _↔_.to r' ∘ _↔_.to r
    ; from = _↔_.from r ∘ _↔_.from r' }

-- equational reasoning combinators

infix  1 begin-↔_
infixr 2 _↔⟨_⟩_
infix  3 _↔-∎

begin-↔_ : ∀ {A B} → A ↔ B → A ↔ B
begin-↔_ A↔B = A↔B

_↔⟨_⟩_ : ∀ A {B C} → A ↔ B → B ↔ C → A ↔ C
A ↔⟨ A↔B ⟩ B↔C =  ↔-trans A↔B B↔C

_↔-∎ : ∀ A → A ↔ A
A ↔-∎ = ↔-refl

⊎-left-identity : ∀ {A} → (⊥ ⊎ A) ↔ A
⊎-left-identity
  = record {
      to = [ (λ ()) , id ]
    ; from = inr }

⊎-right-identity : ∀ {A} → (A ⊎ ⊥) ↔ A
⊎-right-identity
  = record {
      to = [ id , (λ ()) ]
    ; from = inl }

⊎-assoc : ∀ {A B C} → (A ⊎ (B ⊎ C)) ↔ ((A ⊎ B) ⊎ C)
⊎-assoc
  = record {
      to = [ inl ∘ inl , [ inl ∘ inr , inr ] ]
    ; from = [ [ inl , inr ∘ inl ] , inr ∘ inr ] }

⊎-comm : ∀ {A B} → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm
  = record {
      to = [ inr , inl ]
    ; from = [ inr  , inl ] }

⊎-cong : ∀ {A1 A2 B1 B2} → A1 ↔ A2 →
                           B1 ↔ B2 →
                           (A1 ⊎ B1) ↔ (A2 ⊎ B2)
⊎-cong A1↔A2 B1↔B2
  = record {
      to = [ inl ∘ _↔_.to A1↔A2  , inr ∘ _↔_.to B1↔B2 ]
    ; from = [ inl ∘ _↔_.from A1↔A2  , inr ∘ _↔_.from B1↔B2 ] }
