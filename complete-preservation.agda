open import Nat
open import Prelude
open import List
open import core
open import contexts

module complete-preservation where
  -- TODO: convert this into a module imports once proven
  postulate
      preservation : {Δ : hctx} {d d' : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
      typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ


  complete-preservation : {Δ : hctx} {e : hexp} {d d' : dhexp} {τ : htyp} →
             ecomplete e →
             ∅ ⊢ e ⇒ τ ~> d ⊣ Δ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  complete-preservation comp exp step = preservation (typed-expansion-synth exp) step
