open import Nat
open import Prelude
open import List
open import core

module expandability where
  mutual
    expandability-synth : (Γ : tctx) (e : hexp) (τ : htyp) →
                          Γ ⊢ e => τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    expandability-synth = {!!}

    expandability-ana : (Γ : tctx) (e : hexp) (τ : htyp) →
                         Γ ⊢ e => τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    expandability-ana = {!!}
