open import Basics

module NaturalDeduction where

infix  4 _⊢_
infix  4 _⊢_↓
infix  4 _⊢_↑
infix  4 _⊢⁺_↓
infix  4 _⊢⁺_↑

-- Natural deduction inference rules
data _⊢_ : Context → Form → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B

  _∙_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B

  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
    → Γ ⊢ A ∧ B

  fst_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A

  snd_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B

  inl_ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ A ∨ B

  inr_ : ∀ {Γ A B}
    → Γ ⊢ B
    → Γ ⊢ A ∨ B

  case_of_∣_ : ∀ {Γ A B C}
    → Γ ⊢ A ∨ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
    → Γ ⊢ C

  T-intro : ∀ {Γ}
    → Γ ⊢ ⊤

  ⊥-elim : ∀ {Γ C}
    → Γ , ⊥ ⊢ C

-- Normal natural deduction inference rules
-- (bi-directional natural deduction without coercion)
data _⊢_↓ : Context → Form → Set
data _⊢_↑ : Context → Form → Set

data _⊢_↓ where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A ↓

  _∙_  : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B ↑
    → Γ ⊢ A ↑
    → Γ ⊢ B ↓

  fst_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B ↓
    → Γ ⊢ A ↓

  snd_ : ∀ {Γ A B}
    → Γ ⊢ A ∧ B ↓
    → Γ ⊢ B ↓

data _⊢_↑ where

  case_of_∣_ : ∀ {Γ A B C}
    → Γ ⊢ A ∨ B ↓
    → Γ , A ⊢ C ↑
    → Γ , B ⊢ C ↑
    → Γ ⊢ C ↑

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B ↑
    → Γ ⊢ A ⇒ B ↑

  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A ↑
    → Γ ⊢ B ↑
    → Γ ⊢ A ∧ B ↑

  inl_ : ∀ {Γ A B}
    → Γ ⊢ A ↑
    → Γ ⊢ A ∨ B ↑

  inr_ : ∀ {Γ A B}
    → Γ ⊢ B ↑
    → Γ ⊢ A ∨ B ↑

  ⊤-intro : ∀ {Γ}
    → Γ ⊢ ⊤ ↑

  ⊥-elim : ∀ {Γ C}
    → Γ , ⊥ ⊢ C ↑

  ↓↑ : ∀ {Γ A}
    → Γ ⊢ A ↓
    → Γ ⊢ A ↑

-- Proving that bi-directional natural deduction without coercion
-- is sound with respect to the original natural deduction system.
mutual
  ⊢↓-soundness : ∀ {Γ C}
    → Γ ⊢ C ↓
    → Γ ⊢ C
  ⊢↓-soundness (` x)   = ` x
  ⊢↓-soundness (D ∙ x) = ⊢↑-soundness D ∙ ⊢↑-soundness x
  ⊢↓-soundness (fst D) = fst ⊢↓-soundness D
  ⊢↓-soundness (snd D) = snd ⊢↓-soundness D

  ⊢↑-soundness : ∀ {Γ C}
    → Γ ⊢ C ↑
    → Γ ⊢ C
  ⊢↑-soundness (case x of D ∣ D₁) = case ⊢↓-soundness x of ⊢↑-soundness D ∣ ⊢↑-soundness D₁
  ⊢↑-soundness (ƛ D)              = ƛ ⊢↑-soundness D
  ⊢↑-soundness ⟨ D , D₁ ⟩          = ⟨ ⊢↑-soundness D , ⊢↑-soundness D₁ ⟩
  ⊢↑-soundness (inl D)            = inl ⊢↑-soundness D
  ⊢↑-soundness (inr D)            = inr ⊢↑-soundness D
  ⊢↑-soundness ⊤-intro           = T-intro
  ⊢↑-soundness ⊥-elim            = ⊥-elim
  ⊢↑-soundness (↓↑ x)             = ⊢↓-soundness x

-- Extended bi-directional natural deduction inference rules
-- (bi-directional natural deduction with coercion)
data _⊢⁺_↓ : Context → Form → Set
data _⊢⁺_↑ : Context → Form → Set

data _⊢⁺_↓ where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢⁺ A ↓

  _∙_  : ∀ {Γ A B}
    → Γ ⊢⁺ A ⇒ B ↓
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ B ↓

  fst_ : ∀ {Γ A B}
    → Γ ⊢⁺ A ∧ B ↓
    → Γ ⊢⁺ A ↓

  snd_ : ∀ {Γ A B}
     → Γ ⊢⁺ A ∧ B ↓
     → Γ ⊢⁺ B ↓

  ↑↓ : ∀ {Γ A}
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ A ↓

data _⊢⁺_↑ where

  case_of_∣_ : ∀ {Γ A B C}
    → Γ ⊢⁺ A ∨ B ↓
    → Γ , A ⊢⁺ C ↑
    → Γ , B ⊢⁺ C ↑
    → Γ ⊢⁺ C ↑

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢⁺ B ↑
    → Γ ⊢⁺ A ⇒ B ↑

  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ B ↑
    → Γ ⊢⁺ A ∧ B ↑

  inl_ : ∀ {Γ A B}
    → Γ ⊢⁺ A ↑
    → Γ ⊢⁺ A ∨ B ↑

  inr_ : ∀ {Γ A B}
    → Γ ⊢⁺ B ↑
    → Γ ⊢⁺ A ∨ B ↑

  ⊤-intro : ∀ {Γ}
    → Γ ⊢⁺ ⊤ ↑

  ⊥-elim : ∀ {Γ C}
    → Γ , ⊥ ⊢⁺ C ↑

  ↓↑ : ∀ {Γ A}
    → Γ ⊢⁺ A ↓
    → Γ ⊢⁺ A ↑

-- Proving that bi-directional natural deduction system with coercion
-- is sound with respect to the original natural deduction system.
mutual
  ⊢⁺↓-soundness : ∀ {Γ C}
    → Γ ⊢⁺ C ↓
    → Γ ⊢ C
  ⊢⁺↓-soundness (` x)   = ` x
  ⊢⁺↓-soundness (D ∙ x) = ⊢⁺↓-soundness D ∙ ⊢⁺↑-soundness x
  ⊢⁺↓-soundness (fst D) = fst ⊢⁺↓-soundness D
  ⊢⁺↓-soundness (snd D) = snd ⊢⁺↓-soundness D
  ⊢⁺↓-soundness (↑↓ x)  = ⊢⁺↑-soundness x

  ⊢⁺↑-soundness : ∀ {Γ C}
    → Γ ⊢⁺ C ↑
    → Γ ⊢ C
  ⊢⁺↑-soundness (case x of D ∣ D₁)  = case ⊢⁺↓-soundness x of ⊢⁺↑-soundness D ∣ ⊢⁺↑-soundness D₁
  ⊢⁺↑-soundness (ƛ D)               = ƛ ⊢⁺↑-soundness D
  ⊢⁺↑-soundness ⟨ D , D₁ ⟩           = ⟨ ⊢⁺↑-soundness D , ⊢⁺↑-soundness D₁ ⟩
  ⊢⁺↑-soundness (inl D)             = inl ⊢⁺↑-soundness D
  ⊢⁺↑-soundness (inr D)             = inr ⊢⁺↑-soundness D
  ⊢⁺↑-soundness ⊤-intro            = T-intro
  ⊢⁺↑-soundness ⊥-elim             = ⊥-elim
  ⊢⁺↑-soundness (↓↑ x)              = ⊢⁺↓-soundness x

-- Using a record type to represent conjunction in the meta language.
record conj (Γ : Context) (A : Form) : Set where
  field
    proj₁ : Γ ⊢⁺ A ↓
    proj₂ : Γ ⊢⁺ A ↑
open conj

-- Proving that bi-directional natural deduction with coercion
-- is complete with respect to the original natural deduction system.
⊢⁺-completeness : ∀ {Γ A}
  → Γ ⊢ A
  → conj Γ A
⊢⁺-completeness (` x) = record { proj₁ = ` x ; proj₂ = ↓↑ (` x) }
⊢⁺-completeness (ƛ D) = record
                          { proj₁ = ↑↓ (ƛ proj₂ (⊢⁺-completeness D))
                          ; proj₂ = ƛ proj₂ (⊢⁺-completeness D)
                          }
⊢⁺-completeness (D ∙ D₁) = record
                             { proj₁ = proj₁ (⊢⁺-completeness D) ∙ proj₂ (⊢⁺-completeness D₁)
                             ; proj₂ =
                                 ↓↑ (proj₁ (⊢⁺-completeness D) ∙ proj₂ (⊢⁺-completeness D₁))
                             }
⊢⁺-completeness ⟨ D , D₁ ⟩ = record
                               { proj₁ =
                                   ↑↓ ⟨ proj₂ (⊢⁺-completeness D) , proj₂ (⊢⁺-completeness D₁) ⟩
                               ; proj₂ =
                                   ⟨ proj₂ (⊢⁺-completeness D) , proj₂ (⊢⁺-completeness D₁) ⟩
                               }
⊢⁺-completeness (fst D) = record
                            { proj₁ = fst proj₁ (⊢⁺-completeness D)
                            ; proj₂ = ↓↑ (fst proj₁ (⊢⁺-completeness D))
                            }
⊢⁺-completeness (snd D) = record
                            { proj₁ = snd proj₁ (⊢⁺-completeness D)
                            ; proj₂ = ↓↑ (snd proj₁ (⊢⁺-completeness D))
                            }
⊢⁺-completeness (inl D) = record
                            { proj₁ = ↑↓ (inl proj₂ (⊢⁺-completeness D))
                            ; proj₂ = inl proj₂ (⊢⁺-completeness D)
                            }
⊢⁺-completeness (inr D) = record
                            { proj₁ = ↑↓ (inr proj₂ (⊢⁺-completeness D))
                            ; proj₂ = inr proj₂ (⊢⁺-completeness D)
                            }
⊢⁺-completeness (case D of D₁ ∣ D₂) = record
                                        { proj₁ =
                                            ↑↓
                                            (case proj₁ (⊢⁺-completeness D) of proj₂ (⊢⁺-completeness D₁) ∣
                                             proj₂ (⊢⁺-completeness D₂))
                                        ; proj₂ =
                                            case proj₁ (⊢⁺-completeness D) of proj₂ (⊢⁺-completeness D₁) ∣
                                            proj₂ (⊢⁺-completeness D₂)
                                        }
⊢⁺-completeness T-intro = record { proj₁ = ↑↓ ⊤-intro ; proj₂ = ⊤-intro }
⊢⁺-completeness ⊥-elim = record { proj₁ = ↑↓ ⊥-elim ; proj₂ = ⊥-elim }
