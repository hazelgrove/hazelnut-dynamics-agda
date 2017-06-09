open import Nat
open import Prelude
open import List
open import core
open import contexts

module preservation where
  preservation : (Δ : hctx) (d d' : dhexp) (τ : htyp) →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  preservation = {!!}
