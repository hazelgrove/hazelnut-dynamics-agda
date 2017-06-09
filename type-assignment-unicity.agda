open import Nat
open import Prelude
open import List
open import core

module type-assignment-unicity where
  type-assignment-unicity : (Γ : tctx) (d : dhexp) (t' t : htyp) (Δ : hctx) →
                              Δ , Γ ⊢ d :: t →
                              Δ , Γ ⊢ d :: t' →
                              t == t'
  type-assignment-unicity = {!!}
