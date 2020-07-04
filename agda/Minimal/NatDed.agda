open import Basics    hiding (id)
open import Form

module NatDed where

  -- some logical properties

  define-⊥ : (Ctx → Form → Set) → Set
  define-⊥ R = ∀ Γ
         → R Γ `⊥ ↔ (∀ A → R Γ A)

  -- some entailment properties

  Monotonicity : (Ctx → Form → Set) → Set
  Monotonicity R = ∀ {Γ Γ' A}
    → Γ ⊆ Γ'
    → R Γ A
    → R Γ' A

  Reflexivity : (Ctx → Form → Set) → Set
  Reflexivity R = ∀ {Γ A}
    → A ∈ Γ
    → R Γ A

  Cut : (Ctx → Form → Set) → Set
  Cut R = ∀ {Γ A B}
    → R Γ A
    → R (Γ , A) B
    → R Γ B

  Consistency : (Ctx → Form → Set) → Set
  Consistency R = ¬ (R ∅ `⊥)


  -- natural deduction rules

  infix 3 _⊢_
  data _⊢_ : Ctx → Form → Set where

    id   : ∀ {Γ A}
      → A ∈ Γ
      → Γ ⊢ A

    `⊥-e : ∀ {Γ A}
      → Γ ⊢ `⊥
      → Γ ⊢ A

    ⊃-i : ∀ {Γ A B}
      → (Γ , A) ⊢ B
      → Γ ⊢ (A ⊃ B)

    ⊃-e : ∀ {Γ A B}
      → Γ ⊢ (A ⊃ B)
      → Γ ⊢ A
      → Γ ⊢ B

  --------------------------------
  -- proving logical properties --
  --------------------------------

  ⊢-⊥ : define-⊥ _⊢_
  ⊢-⊥ = λ Γ → record { to = λ D A → `⊥-e D ; from = λ f → f `⊥ }

  -----------------------------------
  -- proving entailment properties --
  -----------------------------------

  -- 1. reflexivity

  ⊢-reflexivity : Reflexivity _⊢_
  ⊢-reflexivity = id

  -- 2. monotonicity

  ⊢-monotonicity : Monotonicity _⊢_
  ⊢-monotonicity ex (id x)      = id (ex _ x)
  ⊢-monotonicity ex (`⊥-e x)    = `⊥-e (⊢-monotonicity ex x)
  ⊢-monotonicity ex (⊃-i x)     = ⊃-i (⊢-monotonicity (⊆-inc ex) x)
  ⊢-monotonicity ex (⊃-e x x₁)  = ⊃-e (⊢-monotonicity ex x)
    (⊢-monotonicity ex x₁)

  -- 3. cut

  ⊢-cut : Cut _⊢_
  ⊢-cut D E = ⊃-e (⊃-i E) D

  -- 4. consistency

  ------------------------
  -- semantics approach --
  ------------------------

  -- 1. defining formula semantics

  sem-form : Form → Set
  sem-form `⊥       = ⊥
  sem-form (p ⊃ p₁) = (sem-form p) → (sem-form p₁)

  -- 2. defining context semantics

  sem-ctx : Ctx → Set
  sem-ctx ∅       = ⊤
  sem-ctx (Γ , p) = (sem-form p) × (sem-ctx Γ)

  -- 3. defining variable semantics

  sem-var : ∀ {p Γ}
    → p ∈ Γ
    → sem-ctx Γ
    → sem-form p
  sem-var here      = λ env → fst env
  sem-var (there v) = λ env → sem-var v (snd env)

  -- 4. defining proof semantics

  sem-nd : ∀ {p Γ}
    → Γ ⊢ p
    → sem-ctx Γ
    → sem-form p
  sem-nd (id x)     = λ env   → sem-var x env
  sem-nd (`⊥-e D)   = λ env   → ⊥-elim (sem-nd D env)
  sem-nd (⊃-i D)    = λ env v → sem-nd D (v , env)
  sem-nd (⊃-e D D₁) = λ env   → (sem-nd D env) (sem-nd D₁ env)

  -- 5. proving consistency for natural deduction

  ⊢-consistency₁ : Consistency _⊢_
  ⊢-consistency₁ = λ D → sem-nd D tt
