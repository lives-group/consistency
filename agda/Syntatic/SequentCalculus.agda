open import Relation.Binary.PropositionalEquality
open import ContextPermutation
open import Basics
open import NaturalDeduction

module SequentCalculus where

infix 4 _==>_

-- Inference rules for Sequent Calculus.
data _==>_ : Context → Form → Set where

  init : ∀ {Γ A}
    → Γ , A ==> A

  ∧R : ∀ {Γ A B}
    → Γ ==> A
    → Γ ==> B
    → Γ ==> A ∧ B

  ∧L₁ : ∀ {Γ A B C}
    → Γ , A ∧ B , A ==> C
    → Γ , A ∧ B     ==> C

  ∧L₂ : ∀ {Γ A B C}
    → Γ , A ∧ B , B ==> C
    → Γ , A ∧ B     ==> C

  ⇒R : ∀ {Γ A B}
    → Γ , A ==> B
    → Γ     ==> A ⇒ B

  ⇒L : ∀ {Γ A B C}
    → Γ , A ⇒ B     ==> A
    → Γ , A ⇒ B , B ==> C
    → Γ , A ⇒ B     ==> C

  ∨R₁ : ∀ {Γ A B}
    → Γ ==> A
    → Γ ==> A ∨ B

  ∨R₂ : ∀ {Γ A B}
    → Γ ==> B
    → Γ ==> A ∨ B

  ∨L : ∀ {Γ A B C}
    → Γ , A ∨ B , A ==> C
    → Γ , A ∨ B , B ==> C
    → Γ , A ∨ B     ==> C

  ⊤R : ∀ {Γ}
    → Γ ==> ⊤

  ⊥L : ∀ {Γ C}
    → Γ , ⊥ ==> C

  exchange : ∀ {Γ Δ C}     -- Structural rule
    → Γ ~ Δ
    → Γ ==> C
    → Δ ==> C

-- Proving that Sequent Calculus is consistent.
==>-consistency : ¬ (∅ ==> ⊥)
==>-consistency (exchange x D) rewrite ~-∅ _ x = ==>-consistency D

-- Proving that Sequent Calculus admits weakening.
==>-weakening : ∀ {Γ F C}
  → Γ     ==> C
  → Γ , F ==> C
==>-weakening init      = exchange Swap init
==>-weakening (∧R D D₁) = ∧R (==>-weakening D) (==>-weakening D₁)
==>-weakening (∧L₁ D)   = exchange Swap (∧L₁ (exchange (Trans Swap (Skip Swap)) (==>-weakening D)))
==>-weakening (∧L₂ D)   = exchange Swap (∧L₂ (exchange (Trans Swap (Skip Swap)) (==>-weakening D)))
==>-weakening (⇒R D)    = ⇒R (exchange Swap (==>-weakening D))
==>-weakening (⇒L D D₁) = exchange Swap (⇒L (exchange Swap (==>-weakening D))
  (exchange (Trans Swap (Skip Swap)) (==>-weakening D₁)))
==>-weakening (∨R₁ D)   = ∨R₁ (==>-weakening D)
==>-weakening (∨R₂ D)   = ∨R₂ (==>-weakening D)
==>-weakening (∨L D D₁) = exchange Swap (∨L (exchange (Trans Swap (Skip Swap)) (==>-weakening D))
  (exchange (Trans Swap (Skip Swap)) (==>-weakening D₁)))
==>-weakening ⊤R        = ⊤R
==>-weakening ⊥L        = exchange Swap ⊥L
==>-weakening (exchange D x) = exchange (Skip D) (==>-weakening x)

-- Proving that Sequent Calculus admits contraction.
-- (Here we are using fuel because Agda's termination checker
--  doesn't see that the (exchange D) keeps the size of the derivation D).
==>-contraction : ∀ {Γ A C}
  → ℕ
  → Γ , A , A ==> C
  → Maybe (Γ , A ==> C)
==>-contraction zero _ = nothing
==>-contraction (suc n) init = just init
==>-contraction (suc n) (∧R D D₁) with (==>-contraction n D) | (==>-contraction n D₁)
==>-contraction (suc n) (∧R D D₁) | nothing | nothing = nothing
==>-contraction (suc n) (∧R D D₁) | nothing | just x = nothing
==>-contraction (suc n) (∧R D D₁) | just x | nothing = nothing
==>-contraction (suc n) (∧R D D₁) | just x | just x₁ = just (∧R x x₁)
==>-contraction (suc n) (∧L₁ D) with (==>-contraction n (exchange (Trans Swap (Skip Swap)) D))
==>-contraction (suc n) (∧L₁ D) | nothing = nothing
==>-contraction (suc n) (∧L₁ D) | just x = just (∧L₁ (exchange Swap x))
==>-contraction (suc n) (∧L₂ D) with (==>-contraction n (exchange (Trans Swap (Skip Swap)) D))
==>-contraction (suc n) (∧L₂ D) | nothing = nothing
==>-contraction (suc n) (∧L₂ D) | just x = just (∧L₂ (exchange Swap x))
==>-contraction (suc n) (⇒R D) with (==>-contraction n (exchange (Trans Swap (Skip Swap)) D))
==>-contraction (suc n) (⇒R D) | nothing = nothing
==>-contraction (suc n) (⇒R D) | just x = just (⇒R (exchange Swap x))
==>-contraction (suc n) (⇒L D D₁) with (==>-contraction n D) |
  (==>-contraction n (exchange (Trans Swap (Skip Swap)) D₁))
==>-contraction (suc n) (⇒L D D₁) | nothing | nothing = nothing
==>-contraction (suc n) (⇒L D D₁) | nothing | just x = nothing
==>-contraction (suc n) (⇒L D D₁) | just x | nothing = nothing
==>-contraction (suc n) (⇒L D D₁) | just x | just x₁ = just (⇒L x (exchange Swap x₁))
==>-contraction (suc n) (∨R₁ D) with (==>-contraction n D)
==>-contraction (suc n) (∨R₁ D) | nothing = nothing
==>-contraction (suc n) (∨R₁ D) | just x = just (∨R₁ x)
==>-contraction (suc n) (∨R₂ D) with (==>-contraction n D)
==>-contraction (suc n) (∨R₂ D) | nothing = nothing
==>-contraction (suc n) (∨R₂ D) | just x = just (∨R₂ x)
==>-contraction (suc n) (∨L D D₁) with (==>-contraction n (exchange (Trans Swap (Skip Swap)) D)) |
  (==>-contraction n (exchange (Trans Swap (Skip Swap)) D₁))
==>-contraction (suc n) (∨L D D₁) | nothing | nothing = nothing
==>-contraction (suc n) (∨L D D₁) | nothing | just x = nothing
==>-contraction (suc n) (∨L D D₁) | just x | nothing = nothing
==>-contraction (suc n) (∨L D D₁) | just x | just x₁ = just (∨L (exchange Swap x) (exchange Swap x₁))
==>-contraction (suc n) ⊤R = just ⊤R
==>-contraction (suc n) ⊥L = just ⊥L
==>-contraction (suc n) (exchange x D) with (==>-contraction n (exchange x D))
==>-contraction (suc n) (exchange x D) | nothing = nothing
==>-contraction (suc n) (exchange x D) | just x₁ = just x₁

-- Proving the admissibility of cut.
-- (Here we are using fuel because this proof depends on the result of a ==>contraction)
==>-cut : ∀ {Γ A C}
  → ℕ
  → Γ     ==> A
  → Γ , A ==> C
  → Maybe (Γ ==> C)
==>-cut zero _ _ = nothing
==>-cut (suc n) init E    = ==>-contraction n E
==>-cut (suc n) D init    = just D
==>-cut (suc n) (∧R D D₁) (∧L₁ E) with (==>-cut n (==>-weakening D) E)
==>-cut (suc n) (∧R D D₁) (∧L₁ E) | nothing = nothing
==>-cut (suc n) (∧R D D₁) (∧L₁ E) | just x  = ==>-cut n (∧R D D₁) x
==>-cut (suc n) (∧R D D₁) (∧L₂ E) with ==>-cut n (==>-weakening D₁) E
==>-cut (suc n) (∧R D D₁) (∧L₂ E) | nothing = nothing
==>-cut (suc n) (∧R D D₁) (∧L₂ E) | just x = ==>-cut n (∧R D D₁) x
==>-cut (suc n) (⇒R D) (⇒L E E₁) with (==>-cut n (⇒R D) E)
==>-cut (suc n) (⇒R D) (⇒L E E₁) | nothing = nothing
==>-cut (suc n) (⇒R D) (⇒L E E₁) | just x with (==>-cut n x D)
==>-cut (suc n) (⇒R D) (⇒L E E₁) | just x | nothing = nothing
==>-cut (suc n) (⇒R D) (⇒L E E₁) | just x | just x₁ with (==>-cut n (==>-weakening x₁) E₁)
==>-cut (suc n) (⇒R D) (⇒L E E₁) | just x | just x₁ | nothing = nothing
==>-cut (suc n) (⇒R D) (⇒L E E₁) | just x | just x₁ | just x₂ = ==>-cut n (⇒R D) x₂
==>-cut (suc n) (∨R₁ D) (∨L E E₁) with (==>-cut n (==>-weakening D) E)
==>-cut (suc n) (∨R₁ D) (∨L E E₁) | nothing = nothing
==>-cut (suc n) (∨R₁ D) (∨L E E₁) | just x = ==>-cut n (∨R₁ D) x
==>-cut (suc n) (∨R₂ D) (∨L E E₁) with (==>-cut n (==>-weakening D) E₁)
==>-cut (suc n) (∨R₂ D) (∨L E E₁) | nothing = nothing
==>-cut (suc n) (∨R₂ D) (∨L E E₁) | just x = ==>-cut n (∨R₂ D) x
==>-cut (suc n) (∧L₁ D) E with (==>-cut n D (exchange Swap (==>-weakening E)))
==>-cut (suc n) (∧L₁ D) E | nothing = nothing
==>-cut (suc n) (∧L₁ D) E | just x = just (∧L₁ x)
==>-cut (suc n) (∧L₂ D) E with (==>-cut n D (exchange Swap (==>-weakening E)))
==>-cut (suc n) (∧L₂ D) E | nothing = nothing
==>-cut (suc n) (∧L₂ D) E | just x = just (∧L₂ x)
==>-cut (suc n) (⇒L D D₁) E with (==>-cut n D₁ (exchange Swap (==>-weakening E)))
==>-cut (suc n) (⇒L D D₁) E | nothing = nothing
==>-cut (suc n) (⇒L D D₁) E | just x = just (⇒L D x)
==>-cut (suc n) (∨L D D₁) E
  with (==>-cut n D (exchange Swap (==>-weakening E))) | (==>-cut n D₁ (exchange Swap (==>-weakening E)))
==>-cut (suc n) (∨L D D₁) E | nothing | nothing = nothing
==>-cut (suc n) (∨L D D₁) E | nothing | just x = nothing
==>-cut (suc n) (∨L D D₁) E | just x | nothing = nothing
==>-cut (suc n) (∨L D D₁) E | just x | just x₁ = just (∨L x x₁)
==>-cut (suc n) D (∧R E E₁) with (==>-cut n D E) | (==>-cut n D E₁)
==>-cut (suc n) D (∧R E E₁) | nothing | nothing = nothing
==>-cut (suc n) D (∧R E E₁) | nothing | just x = nothing
==>-cut (suc n) D (∧R E E₁) | just x | nothing = nothing
==>-cut (suc n) D (∧R E E₁) | just x | just x₁ = just (∧R x x₁)
==>-cut (suc n) D (⇒R E) with (==>-cut n (==>-weakening D) (exchange Swap E))
==>-cut (suc n) D (⇒R E) | nothing = nothing
==>-cut (suc n) D (⇒R E) | just x = just (⇒R x)
==>-cut (suc n) D (∨R₁ E) with (==>-cut n D E)
==>-cut (suc n) D (∨R₁ E) | nothing = nothing
==>-cut (suc n) D (∨R₁ E) | just x = just (∨R₁ x)
==>-cut (suc n) D (∨R₂ E) with (==>-cut n D E)
==>-cut (suc n) D (∨R₂ E) | nothing = nothing
==>-cut (suc n) D (∨R₂ E) | just x = just (∨R₂ x)
==>-cut (suc n) ⊤R E = ==>-cut n ⊤R E
==>-cut (suc n) _ ⊤R = just ⊤R
==>-cut (suc n) ⊥L _ = just ⊥L
==>-cut (suc n) D ⊥L = ==>-cut n D ⊥L
==>-cut (suc n) (exchange x D) E = ==>-cut n (exchange x D) E
==>-cut (suc n) D (exchange x E) = ==>-cut n D (exchange x E)

-- Translating Natural Deduction to Sequent Calculus derivations.
-- (Here we are using fuel because this proof depends on the result of a ==>-cut)
⊢-translation : ∀ {Γ C}
  → ℕ
  → Γ ⊢ C
  → Maybe (Γ ==> C)
⊢-translation zero _ = nothing
⊢-translation (suc n) (` x) = ⊢-translation n (` x)
⊢-translation (suc n) (ƛ D) with (⊢-translation n D)
⊢-translation (suc n) (ƛ D) | nothing = nothing
⊢-translation (suc n) (ƛ D) | just x = just (⇒R x)
⊢-translation (suc n) (D ∙ D₁) with (⊢-translation n D) | (⊢-translation n D₁)
⊢-translation (suc n) (D ∙ D₁) | nothing | nothing = nothing
⊢-translation (suc n) (D ∙ D₁) | nothing | just x = nothing
⊢-translation (suc n) (D ∙ D₁) | just x | nothing = nothing
⊢-translation (suc n) (D ∙ D₁) | just x | just x₁ = ==>-cut n x (⇒L (==>-weakening x₁) init)
⊢-translation (suc n) ⟨ D , D₁ ⟩ with (⊢-translation n D) | (⊢-translation n D₁)
⊢-translation (suc n) ⟨ D , D₁ ⟩ | nothing | nothing = nothing
⊢-translation (suc n) ⟨ D , D₁ ⟩ | nothing | just x = nothing
⊢-translation (suc n) ⟨ D , D₁ ⟩ | just x | nothing = nothing
⊢-translation (suc n) ⟨ D , D₁ ⟩ | just x | just x₁ = just (∧R x x₁)
⊢-translation (suc n) (fst D) with (⊢-translation n D)
⊢-translation (suc n) (fst D) | nothing = nothing
⊢-translation (suc n) (fst D) | just x = ==>-cut n x (∧L₁ init)
⊢-translation (suc n) (snd D) with (⊢-translation n D)
⊢-translation (suc n) (snd D) | nothing = nothing
⊢-translation (suc n) (snd D) | just x = ==>-cut n x (∧L₂ init)
⊢-translation (suc n) (inl D) with (⊢-translation n D)
⊢-translation (suc n) (inl D) | nothing = nothing
⊢-translation (suc n) (inl D) | just x = just (∨R₁ x)
⊢-translation (suc n) (inr D) with (⊢-translation n D)
⊢-translation (suc n) (inr D) | nothing = nothing
⊢-translation (suc n) (inr D) | just x = just (∨R₂ x)
⊢-translation (suc n) (case D of D₁ ∣ D₂)
  with (⊢-translation n D) | (⊢-translation n D₁) | (⊢-translation n D₂)
⊢-translation (suc n) (case D of D₁ ∣ D₂) | nothing | nothing | nothing = nothing
⊢-translation (suc n) (case D of D₁ ∣ D₂) | nothing | nothing | just x = nothing
⊢-translation (suc n) (case D of D₁ ∣ D₂) | nothing | just x | nothing = nothing
⊢-translation (suc n) (case D of D₁ ∣ D₂) | nothing | just x | just x₁ = nothing
⊢-translation (suc n) (case D of D₁ ∣ D₂) | just x | nothing | nothing = nothing
⊢-translation (suc n) (case D of D₁ ∣ D₂) | just x | nothing | just x₁ = nothing
⊢-translation (suc n) (case D of D₁ ∣ D₂) | just x | just x₁ | nothing = nothing
⊢-translation (suc n) (case D of D₁ ∣ D₂) | just x | just x₁ | just x₂ =
  ==>-cut n x (∨L (exchange Swap (==>-weakening x₁)) (exchange Swap (==>-weakening x₂)))
⊢-translation (suc n) T-intro = just ⊤R
⊢-translation (suc n) ⊥-elim = just  ⊥L

==>-consistency' : ℕ → Maybe (¬ (∅ ==> ⊥))
==>-consistency' zero = nothing
==>-consistency' (suc n) = just ==>-consistency

-- Proving the consistency property for Natural Deduction.
-- (Here we are using fuel because this proof dependes on the result of a ⊢-translation)
⊢-consistency : ℕ → Maybe (¬ (∅ ⊢ ⊥))
⊢-consistency zero = nothing
⊢-consistency (suc n) = just λ p → let
                                        p1 : Maybe (∅ ==> ⊥)
                                        p1 = ⊢-translation (suc n) p
                                   in maybe ==>-consistency impossible p1  
                             where
                               postulate impossible : bottom
