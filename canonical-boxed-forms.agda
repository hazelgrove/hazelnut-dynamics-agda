open import Nat
open import Prelude
open import contexts
open import core


module canonical-boxed-forms where
  canonical-boxed-forms-b : ∀{Δ d} →
                            Δ , ∅ ⊢ d :: b →
                            d boxedval →
                            d == c
  canonical-boxed-forms-b = {!!}

  canonical-boxed-forms-arr : ∀{Δ d τ1 τ2 } →
                            Δ , ∅ ⊢ d :: (τ1 ==> τ2)  →
                            d boxedval →
                            (Σ[ x ∈ Nat ] Σ[ d' ∈ dhexp ] (d == (·λ x [ τ1 ] d') ×
                                                           Δ , ■ (x , τ1) ⊢ d' :: τ2)) +
                            (Σ[ d' ∈ dhexp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ] (d == (d' ⟨ τ1' ==> τ2' ⇒ τ1 ==> τ2 ⟩) ×
                                                                             (τ1' ==> τ2' ≠ τ1 ==> τ2) ×
                                                                             (Δ , ∅ ⊢ d' :: τ1' ==> τ2')))
  canonical-boxed-forms-arr = {!!}

  canonical-boxed-forms-hole : ∀{Δ d} →
                               Δ , ∅ ⊢ d :: ⦇⦈ →
                               d boxedval →
                               Σ[ d' ∈ dhexp ] Σ[ τ' ∈ htyp ] ((d == d' ⟨ τ' ⇒ ⦇⦈ ⟩) ×
                                                               (τ' ground) ×
                                                               (Δ , ∅ ⊢ d' :: τ'))
  canonical-boxed-forms-hole = {!!}
