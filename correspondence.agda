open import Nat
open import Prelude
open import List
open import core

module correspondence where
  mutual
    correspondence-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Γ ⊢ e => τ
    correspondence-synth ESConst = SConst
    correspondence-synth (ESVar x₁) = SVar x₁
    correspondence-synth (ESLam ex) with correspondence-synth ex
    ... | ih = SLam {!!} ih
    correspondence-synth (ESAp1 x x₁ x₂ x₃) = {!!}
    correspondence-synth (ESAp2 x ex x₁ x₂) = {!!}
    correspondence-synth (ESAp3 x ex x₁) = {!!}
    correspondence-synth ESEHole = SEHole
    correspondence-synth (ESNEHole ex) = SNEHole (correspondence-synth ex)
    correspondence-synth (ESAsc1 x x₁) = {!!}
    correspondence-synth (ESAsc2 x) = {!!}

    correspondence-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx}  →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          Γ ⊢ e <= τ
    correspondence-ana (EALam ex) with correspondence-ana ex
    ... | ih = ALam {!!} {!!} {!!}
    correspondence-ana (EASubsume x x₁ x₂ x₃) = {!!}
    correspondence-ana EAEHole = {!!}
    correspondence-ana (EANEHole x x₁) = {!!}
