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
    expandability-synth Γ .c .b SConst = c , (λ x → None) , ESConst
    expandability-synth Γ _ τ (SAsc x) = {!!} , {!!} , {!!}
    expandability-synth Γ _ τ (SVar x) = {!!}
    expandability-synth Γ _ τ (SAp D x x₁) = {!!}
    expandability-synth Γ _ .⦇⦈ SEHole = {!!}
    expandability-synth Γ _ .⦇⦈ (SNEHole D) = {!!}
    expandability-synth Γ _ _ (SLam x₁ D) = {!!}

    expandability-ana : (Γ : tctx) (e : hexp) (τ : htyp) →
                         Γ ⊢ e => τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    expandability-ana = {!!}
