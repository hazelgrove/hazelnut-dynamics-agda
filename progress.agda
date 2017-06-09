open import Nat
open import Prelude
open import List
open import core
open import contexts

module progress where
  progress : (Δ : hctx) (d : dhexp) (t : htyp) →
             Δ , ∅ ⊢ d :: t →
             d val + d indet + d err[ Δ ] + Σ[ d' ∈ dhexp ] (d ↦ d')
  progress = {!!}
