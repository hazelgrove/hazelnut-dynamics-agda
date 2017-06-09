open import Nat
open import Prelude
open import List
open import core

module typed-expansion where
  mutual
    typed-expansion-synth : (Γ : tctx) (e : hexp) (τ : htyp) (d : dhexp) (Δ : hctx) →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth = {!!}

    typed-expansion-ana : (Γ : tctx) (e : hexp) (τ τ' : htyp) (d : dhexp) (Δ : hctx) →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ ~ τ') × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana = {!!}
