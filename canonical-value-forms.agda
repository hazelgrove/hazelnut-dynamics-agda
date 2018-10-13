open import Nat
open import Prelude
open import contexts
open import core

module canonical-value-forms where
  canonical-value-forms-b : ∀{Δ d} →
                            Δ , ∅ ⊢ d :: b →
                            d val →
                            d == c
  canonical-value-forms-b TAConst VConst = refl
  canonical-value-forms-b (TAVar x₁) ()
  canonical-value-forms-b (TAAp wt wt₁) ()
  canonical-value-forms-b (TAEHole x x₁) ()
  canonical-value-forms-b (TANEHole x wt x₁) ()
  canonical-value-forms-b (TACast wt x) ()
  canonical-value-forms-b (TAFailedCast wt x x₁ x₂) ()

  canonical-value-forms-arr : ∀{Δ d τ1 τ2} →
                              Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                              d val →
                              Σ[ x ∈ Nat ] Σ[ d' ∈ ihexp ]
                                ((d == (·λ x [ τ1 ] d')) ×
                                 (Δ , ■ (x , τ1) ⊢ d' :: τ2))
  canonical-value-forms-arr (TAVar x₁) ()
  canonical-value-forms-arr (TALam _ wt) VLam = _ , _ , refl , wt
  canonical-value-forms-arr (TAAp wt wt₁) ()
  canonical-value-forms-arr (TAEHole x x₁) ()
  canonical-value-forms-arr (TANEHole x wt x₁) ()
  canonical-value-forms-arr (TACast wt x) ()
  canonical-value-forms-arr (TAFailedCast x x₁ x₂ x₃) ()

  -- this argues (somewhat informally, because you still have to inspect
  -- the types of the theorems above and manually verify this property)
  -- that we didn't miss any cases above; this intentionally will make this
  -- file fail to typecheck if we added more types, hopefully forcing us to
  -- remember to add canonical forms lemmas as appropriate
  canonical-value-forms-coverage1 : ∀{Δ d τ} →
                                   Δ , ∅ ⊢ d :: τ →
                                   d val →
                                   τ ≠ b →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                   ⊥
  canonical-value-forms-coverage1 TAConst VConst = λ z _ → z refl
  canonical-value-forms-coverage1 (TAVar x₁) ()
  canonical-value-forms-coverage1 (TALam _ wt) VLam = λ _ z → z _ _ refl
  canonical-value-forms-coverage1 (TAAp wt wt₁) ()
  canonical-value-forms-coverage1 (TAEHole x x₁) ()
  canonical-value-forms-coverage1 (TANEHole x wt x₁) ()
  canonical-value-forms-coverage1 (TACast wt x) ()
  canonical-value-forms-coverage1 (TAFailedCast wt x x₁ x₂) ()

  canonical-value-forms-coverage2 : ∀{Δ d} →
                                   Δ , ∅ ⊢ d :: ⦇⦈ →
                                   d val →
                                   ⊥
  canonical-value-forms-coverage2 (TAVar x₁) ()
  canonical-value-forms-coverage2 (TAAp wt wt₁) ()
  canonical-value-forms-coverage2 (TAEHole x x₁) ()
  canonical-value-forms-coverage2 (TANEHole x wt x₁) ()
  canonical-value-forms-coverage2 (TACast wt x) ()
  canonical-value-forms-coverage2 (TAFailedCast wt x x₁ x₂) ()
