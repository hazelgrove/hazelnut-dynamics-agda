open import Nat
open import Prelude
open import List
open import core

module expansion-generality where
  mutual
    expansion-generality-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Γ ⊢ e => τ
    expansion-generality-synth ESConst = SConst
    expansion-generality-synth (ESVar x₁) = SVar x₁
    expansion-generality-synth (ESLam apt ex) with expansion-generality-synth ex
    ... | ih = SLam apt ih
    expansion-generality-synth (ESAp _ a x₁ x₂ x₃) = SAp a x₁ (expansion-generality-ana x₃)
    expansion-generality-synth ESEHole = SEHole
    expansion-generality-synth (ESNEHole ex) = SNEHole (expansion-generality-synth ex)
    expansion-generality-synth (ESAsc x) = SAsc (expansion-generality-ana x)

    expansion-generality-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          Γ ⊢ e <= τ
    expansion-generality-ana (EALam apt m ex) = ALam apt m (expansion-generality-ana ex)
    expansion-generality-ana (EASubsume x x₁ x₂ x₃) = ASubsume (expansion-generality-synth x₂) x₃
    expansion-generality-ana EAEHole = ASubsume SEHole TCHole1
    expansion-generality-ana (EANEHole x) = ASubsume (SNEHole (expansion-generality-synth x)) TCHole1
