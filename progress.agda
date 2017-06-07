open import Nat
open import Prelude
open import List
open import core

module progress where
  progress : (Δ : ·ctx) (e : ë) (t : τ̇) →
             Δ , ∅ ⊢ e :: t →
             e val + e indet + e err[ Δ ] + Σ[ e' ∈ ë ] (e ↦ e')
  progress = {!!}
