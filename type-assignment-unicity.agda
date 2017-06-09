open import Nat
open import Prelude
open import List
open import core

module type-assignment-unicity where
  type-assignment-unicity : (Γ : tctx) (d : dhexp) (τ' τ : htyp) (Δ : hctx) →
                              Δ , Γ ⊢ d :: τ →
                              Δ , Γ ⊢ d :: τ' →
                              τ == τ'
  type-assignment-unicity = {!!}
