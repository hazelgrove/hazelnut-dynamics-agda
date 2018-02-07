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

  canonical-value-forms-arr : ∀{Δ d τ1 τ2} →
                              Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                              d val →
                              Σ[ x ∈ Nat ] Σ[ d' ∈ dhexp ]
                                ((d == (·λ x [ τ1 ] d')) × (Δ , ■ (x , τ1) ⊢ d' :: τ2))
  canonical-value-forms-arr (TAVar x₁) ()
  canonical-value-forms-arr (TALam wt) VLam = _ , _ , refl , wt
  canonical-value-forms-arr (TAAp wt wt₁) ()
  canonical-value-forms-arr (TAEHole x x₁) ()
  canonical-value-forms-arr (TANEHole x wt x₁) ()
  canonical-value-forms-arr (TACast wt x) ()



  -- this argues (somewhat informally) that we didn't miss any cases above;
  -- this intentionally will make this file fail to typecheck if we added
  -- more types, hopefully forcing us to remember to add canonical forms
  -- lemmas as appropriate
  canonical-value-forms-coverage1 : ∀{Δ d τ} →
                                   Δ , ∅ ⊢ d :: τ →
                                   d val →
                                   τ ≠ b →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                   ⊥
  canonical-value-forms-coverage1 TAConst VConst nb na = nb refl
  canonical-value-forms-coverage1 (TAVar x₁) () nb na
  canonical-value-forms-coverage1 (TALam wt) VLam nb na = na _ _ refl
  canonical-value-forms-coverage1 (TAAp wt wt₁) () nb na
  canonical-value-forms-coverage1 (TAEHole x x₁) () nb na
  canonical-value-forms-coverage1 (TANEHole x wt x₁) () nb na
  canonical-value-forms-coverage1 (TACast wt x) () nb na

  canonical-value-forms-coverage2 : ∀{Δ d} →
                                   Δ , ∅ ⊢ d :: ⦇⦈ →
                                   d val →
                                   ⊥
  canonical-value-forms-coverage2 (TAVar x₁) ()
  canonical-value-forms-coverage2 (TAAp wt wt₁) ()
  canonical-value-forms-coverage2 (TAEHole x x₁) ()
  canonical-value-forms-coverage2 (TANEHole x wt x₁) ()
  canonical-value-forms-coverage2 (TACast wt x) ()
