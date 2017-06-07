open import Nat
open import Prelude
open import List
open import core
open import contexts

module preservation where
  preservation : (Δ : hctx) (e e' : ë) (t : τ̇) →
             Δ , ∅ ⊢ e :: t →
             e ↦ e' →
             Δ , ∅ ⊢ e' :: t
  preservation = {!!}
