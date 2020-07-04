open import Lemmas
open import Basics

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module ContextPermutation where

-- Defining permutation.
data _~_ : Context -> Context -> Set where
  Done  : ∅ ~ ∅
  Skip  : ∀ {t Γ Γ'} -> Γ ~ Γ' -> (Γ , t) ~ (Γ' , t)
  Swap  : ∀ {t t' Γ} -> (Γ , t , t') ~ (Γ , t' , t)
  Trans : ∀ {Γ Γ₁ Γ'} -> Γ ~ Γ₁ -> Γ₁ ~ Γ' -> Γ ~ Γ'

-- Proving that permutation is an equivalence relation.
~-refl : ∀ {Γ} -> Γ ~ Γ
~-refl {∅} = Done
~-refl {Γ , t} = Skip ~-refl

~-sym : ∀ {Γ Γ'} ->  Γ ~ Γ' ->  Γ' ~ Γ
~-sym Done = Done
~-sym (Skip prf) = Skip (~-sym prf)
~-sym Swap = Swap
~-sym (Trans prf prf₁)
   = Trans (~-sym prf₁) (~-sym prf)

~-trans : ∀ {Γ Γ₁ Γ'} ->  Γ ~ Γ₁ ->  Γ₁ ~ Γ' -> Γ ~ Γ'
~-trans p1 p2 = Trans p1 p2

-- Proving that permutation preserves lookup.
~-lookup : ∀ {Γ Γ' t} -> Γ ~ Γ' -> Γ ∋ t -> Γ' ∋ t
~-lookup (Skip perm) Z = Z
~-lookup (Skip perm) (S pl) = S ~-lookup perm pl
~-lookup Swap Z = S Z
~-lookup (Swap {t} {t'}) (S_ {Γ}{t1}.{t'} pl) with t1 ≟F t
~-lookup (Swap {t} {t'}) (S_ {.(_ , t)} {_} {.t'} Z) | no ¬p = Z
~-lookup (Swap {t} {t'}) (S_ {.(_ , t)} {_} {.t'} (S pl)) | no ¬p = S (S pl)
~-lookup (Swap {t} {t'}) (S_ {.(_ , t)} {_} {.t'} pl) | yes p rewrite p = Z
~-lookup (Trans perm perm₁) pl = ~-lookup perm₁ (~-lookup perm pl)

-- A lemma necessary for proving the consistency
-- of Sequent Calculus.
~-∅ : ∀ Γ → Γ ~ ∅ → Γ ≡ ∅
~-∅ ∅ p = refl
~-∅ (Γ , x) (Trans p p₁) with ~-∅ _ p₁
...| refl  = ~-∅ _ p
