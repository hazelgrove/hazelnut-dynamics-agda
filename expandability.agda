open import Nat
open import Prelude
open import List
open import core

module expandability where
  mutual
    expandability-synth : (Γ : tctx) (e : ė) (t : τ̇) →
                          Γ ⊢ e => t →
                          Σ[ e' ∈ ë ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ t ~> e' ⊣ Δ)
    expandability-synth = {!!}

    expandability-ana : (Γ : tctx) (e : ė) (t : τ̇) →
                         Γ ⊢ e => t →
                          Σ[ e' ∈ ë ] Σ[ Δ ∈ hctx ] Σ[ t' ∈ τ̇ ]
                            (Γ ⊢ e ⇐ t ~> e' :: t' ⊣ Δ)
    expandability-ana = {!!}
