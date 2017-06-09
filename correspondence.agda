open import Nat
open import Prelude
open import List
open import core

module correspondence where
  mutual
    correspondence-synth : (Γ : tctx) (e : hexp) (τ : htyp) (d : dhexp) (Δ : hctx) →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Γ ⊢ e => τ
    correspondence-synth = {!!}

    correspondence-ana : (Γ : tctx) (e : hexp) (τ τ' : htyp) (d : dhexp) (Δ : hctx)  →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          Γ ⊢ e => τ
    correspondence-ana = {!!}
