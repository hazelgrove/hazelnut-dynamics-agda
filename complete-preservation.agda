open import Nat
open import Prelude
open import List
open import core
open import contexts

module complete-preservation where
  complete-preservation : {Δ : hctx} {e : hexp} {d d' : dhexp} {τ : htyp} →
             ecomplete e →
             ∅ ⊢ e ⇒ τ ~> d ⊣ Δ →
             Δ ⊢ d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  complete-preservation = {!!}
