open import Data.Product
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Basics hiding (_,_)

module Lemmas where

-- Equality inversion lemmas
≡-=>-inv : ∀ {t1 t2 t1' t2'} -> (t1 ⇒ t2) ≡ (t1' ⇒ t2') -> t1 ≡ t1' × t2 ≡ t2'
≡-=>-inv refl = refl , refl

≡-∧-inv : ∀ {t1 t2 t1' t2'} -> (t1 ∧ t2) ≡ (t1' ∧ t2') -> t1 ≡ t1' × t2 ≡ t2'
≡-∧-inv refl = refl , refl

≡-∨-inv : ∀ {t1 t2 t1' t2'} -> (t1 ∨ t2) ≡ (t1' ∨ t2') -> t1 ≡ t1' × t2 ≡ t2'
≡-∨-inv refl = refl , refl

-- Equality is decidable for Form
_≟F_ : ∀ (t t' : Form) -> Dec (t ≡ t')
⊤ ≟F ⊤ = yes refl
⊤ ≟F (t' ⇒ t'') = no (λ ())
⊤ ≟F (t' ∧ t'') = no (λ ())
⊤ ≟F (t' ∨ t'') = no (λ ())
⊤ ≟F ⊥ = no (λ ())
(t ⇒ t₁) ≟F ⊤ = no (λ ())
(t ⇒ t₁) ≟F (t' ⇒ t'') with t ≟F t' | t₁ ≟F t''
((t ⇒ t₁) ≟F (t' ⇒ t'')) | no ¬p | q = no (¬p ∘ proj₁ ∘ ≡-=>-inv)
((t ⇒ t₁) ≟F (t' ⇒ t'')) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ ≡-=>-inv)
((t ⇒ t₁) ≟F (t' ⇒ t'')) | yes p | yes p₁ rewrite p | p₁ = yes refl
(t ⇒ t₁) ≟F (t' ∧ t'') = no (λ ())
(t ⇒ t₁) ≟F (t' ∨ t'') = no (λ ())
(t ⇒ t₁) ≟F ⊥ = no (λ ())
(t ∧ t₁) ≟F ⊤ = no (λ ())
(t ∧ t₁) ≟F (t' ⇒ t'') = no (λ ())
(t ∧ t₁) ≟F (t' ∧ t'') with t ≟F t' | t₁ ≟F t''
((t ∧ t₁) ≟F (t' ∧ t'')) | no ¬p | q = no (¬p ∘ proj₁ ∘ ≡-∧-inv)
((t ∧ t₁) ≟F (t' ∧ t'')) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ ≡-∧-inv)
((t ∧ t₁) ≟F (t' ∧ t'')) | yes p | yes p₁ rewrite p | p₁ = yes refl
(t ∧ t₁) ≟F (t' ∨ t'') = no (λ ())
(t ∧ t₁) ≟F ⊥ = no (λ ())
(t ∨ t₁) ≟F ⊤ = no (λ ())
(t ∨ t₁) ≟F (t' ⇒ t'') = no (λ ())
(t ∨ t₁) ≟F (t' ∧ t'') = no (λ ())
(t ∨ t₁) ≟F (t' ∨ t'') with t ≟F t' | t₁ ≟F t''
((t ∨ t₁) ≟F (t' ∨ t'')) | no ¬p | q = no (¬p ∘ proj₁ ∘ ≡-∨-inv)
((t ∨ t₁) ≟F (t' ∨ t'')) | yes p | no ¬p = no (¬p ∘ proj₂ ∘ ≡-∨-inv)
((t ∨ t₁) ≟F (t' ∨ t'')) | yes p | yes p₁ rewrite p | p₁ = yes refl
(t ∨ t₁) ≟F ⊥ = no (λ ())
⊥ ≟F ⊤ = no (λ ())
⊥ ≟F (t' ⇒ t'') = no (λ ())
⊥ ≟F (t' ∧ t'') = no (λ ())
⊥ ≟F (t' ∨ t'') = no (λ ())
⊥ ≟F ⊥ = yes refl
