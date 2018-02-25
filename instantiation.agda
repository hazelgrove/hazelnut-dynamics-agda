open import Prelude
open import core

module instantiation where
  instantiation : ∀{ Δ Γ d τ} →
                  Δ , Γ ⊢ d :: τ →
