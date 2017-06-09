open import Nat
open import Prelude
open import List
open import core
open import contexts

module preservation where
  preservation : (Δ : hctx) (d d' : dhexp) (t : htyp) →
             Δ , ∅ ⊢ d :: t →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: t
  preservation = {!!}
