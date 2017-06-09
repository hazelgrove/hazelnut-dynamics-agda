open import Nat
open import Prelude
open import List
open import core
open import contexts

module progress where
  progress : (Δ : hctx) (d : dhexp) (τ : htyp) →
             Δ , ∅ ⊢ d :: τ →
             d val + d indet + d err[ Δ ] + Σ[ d' ∈ dhexp ] (d ↦ d')
  progress = {!!}
