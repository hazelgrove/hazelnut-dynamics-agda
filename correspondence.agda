open import Nat
open import Prelude
open import List
open import core

module correspondence where
  mutual
    correspondence-synth : (Γ : ·ctx) (e : ė) (t : τ̇) (e' : ë) (Δ : ·ctx) →
                            Γ ⊢ e ⇒ t ~> e' ⊣ Δ →
                            Γ ⊢ e => t
    correspondence-synth = {!!}

    correspondence-ana : (Γ : ·ctx) (e : ė) (t : τ̇) (e' : ë) (Δ : ·ctx) (t' : τ̇) →
                          Γ ⊢ e ⇐ t ~> e' :: t' ⊣ Δ →
                          Γ ⊢ e => t
    correspondence-ana = {!!}
