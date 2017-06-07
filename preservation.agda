open import Nat
open import Prelude
open import List
open import core

module preservation where
  preservation : (Δ : ·ctx) (e e' : ë) (t : τ̇) →
             Δ , ∅ ⊢ e :: t →
             e ↦ e' →
             Δ , ∅ ⊢ e' :: t
  preservation = {!!}
