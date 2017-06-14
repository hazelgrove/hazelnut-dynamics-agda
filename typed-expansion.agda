open import Nat
open import Prelude
open import List
open import core

module typed-expansion where
  mutual
    typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth ESConst = TAConst
    typed-expansion-synth (ESVar x₁) = TAVar x₁
    typed-expansion-synth (ESLam x₁ ex) = {!!}
    typed-expansion-synth (ESAp1 x x₁ x₂ x₃) = {!!}
    typed-expansion-synth (ESAp2 x ex x₁ x₂) = {!!}
    typed-expansion-synth (ESAp3 x ex x₁) = {!!}
    typed-expansion-synth ESEHole = {!!}
    typed-expansion-synth (ESNEHole ex) = {!!}
    typed-expansion-synth (ESAsc1 x x₁) = {!!}
    typed-expansion-synth (ESAsc2 x) = {!!}

    typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ ~ τ') × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana (EALam x₁ ex) = {!!}
    typed-expansion-ana (EASubsume x x₁ x₂ x₃) = {!!}
    typed-expansion-ana EAEHole = {!!}
    typed-expansion-ana (EANEHole x x₁) = {!!}
