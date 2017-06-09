open import Nat
open import Prelude
open import List
open import core

module expansion-unicity where
  mutual
    expansion-unicity-synth : (Γ : tctx) (e : hexp) (τ1 τ2 : htyp) (d1 d2 : dhexp) (Δ1 Δ2 : hctx) →
                            Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
                            Γ ⊢ e ⇒ τ2 ~> d2 ⊣ Δ2 →
                            τ1 == τ2 × d1 == d2 × Δ1 == Δ2
    expansion-unicity-synth = {!!}

    expansion-unicity-ana : (Γ : tctx) (e : hexp) (τ1 τ1' τ2 τ2' : htyp) (d1 d2 : dhexp) (Δ1 Δ2 : hctx) →
                          Γ ⊢ e ⇐ τ1 ~> d1 :: τ1' ⊣ Δ1 →
                          Γ ⊢ e ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
                          τ1 == τ2 × d1 == d2 × τ1' == τ2' × Δ1 == Δ2
    expansion-unicity-ana = {!!}
