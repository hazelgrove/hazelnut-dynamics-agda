open import Nat
open import Prelude
open import contexts
open import core

module canonical-value-forms where
  canonical-value-forms-b : ∀{Δ d} →
                            Δ , ∅ ⊢ d :: b →
                            d val →
                            d == c
  canonical-value-forms-b = {!!}

  canonical-value-forms-arr : ∀{Δ d τ1 τ2} →
                              Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                              d val →
                              Σ[ x ∈ Nat ] Σ[ d' ∈ dhexp ]
                                (d == (·λ x [ τ1 ] d') × Δ , ■ (x , τ2) ⊢ d' :: τ2)
  canonical-value-forms-arr = {!!}
