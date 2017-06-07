open import Nat
open import Prelude
open import List
open import core

module expandability where
  mutual
    expandability-synth : (Γ : ·ctx) (e : ė) (t : τ̇) →
                          Γ ⊢ e => t →
                          Σ[ e' ∈ ë ] Σ[ Δ ∈ ·ctx ]
                            (Γ ⊢ e ⇒ t ~> e' ⊣ Δ)
    expandability-synth = {!!}

    expandability-ana : (Γ : ·ctx) (e : ė) (t : τ̇) →
                         Γ ⊢ e => t →
                          Σ[ e' ∈ ë ] Σ[ Δ ∈ ·ctx ] Σ[ t' ∈ τ̇ ]
                            (Γ ⊢ e ⇐ t ~> e' :: t' ⊣ Δ)
    expandability-ana = {!!}
