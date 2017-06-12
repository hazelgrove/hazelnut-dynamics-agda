open import Nat
open import Prelude
open import List
open import core

module typed-expansion where
  mutual
    typed-expansion-synth : (Γ : tctx) (e : hexp) (τ : htyp) (d : dhexp) (Δ : hctx) →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth Γ .c .b .c .(λ _ → None) ESConst = TAConst
    typed-expansion-synth _ _ τ _ .(λ _ → None) ESVar = TAVar
    typed-expansion-synth Γ _ _ _ .(λ _ → None) (ESLam D) with typed-expansion-synth _ _ _ _ _ D
    ... | ih = TALam {!!}
    typed-expansion-synth Γ _ .⦇⦈ _ _ (ESAp1 y x x₁ x₂) = {!!}
    typed-expansion-synth Γ _ τ _ _ (ESAp2 y D x x₁) = {!!}
    typed-expansion-synth Γ _ τ _ _ (ESAp3 y D x) = {!!}
    typed-expansion-synth Γ _ .⦇⦈ _ _ ESEHole = TAEHole {!!}
    typed-expansion-synth Γ _ .⦇⦈ _ _ (ESNEHole D) = TANEHole {!!} {!!}
    typed-expansion-synth Γ _ τ _ Δ (ESAsc1 x x₁) = {!!}
    typed-expansion-synth Γ _ τ d Δ (ESAsc2 x) = {!!}

    typed-expansion-ana : (Γ : tctx) (e : hexp) (τ τ' : htyp) (d : dhexp) (Δ : hctx) →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ ~ τ') × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana Γ _ _ _ _ Δ (EALam D) = (TCArr TCRefl {!!}) , {!!}
    typed-expansion-ana Γ e τ τ' d Δ (EASubsume x x₁ x₂ x₃) = {!!}
    typed-expansion-ana Γ _ τ' .τ' _ _ EAEHole = TCRefl , {!!}
    typed-expansion-ana Γ _ τ' .τ' _ _ (EANEHole x x₁) = TCRefl , {!!}
