open import Nat
open import Prelude
open import List
open import core

module expandability where
  mutual
    expandability-synth : (Γ : tctx) (e : hexp) (t : htyp) →
                          Γ ⊢ e => t →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ t ~> d ⊣ Δ)
    expandability-synth = {!!}

    expandability-ana : (Γ : tctx) (e : hexp) (t : htyp) →
                         Γ ⊢ e => t →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ] Σ[ t' ∈ htyp ]
                            (Γ ⊢ e ⇐ t ~> d :: t' ⊣ Δ)
    expandability-ana = {!!}
