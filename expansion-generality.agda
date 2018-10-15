open import Nat
open import Prelude
open import core
open import disjointness

module expansion-generality where
  mutual
    expansion-generality-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : ihexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Γ ⊢ e => τ
    expansion-generality-synth ESConst = SConst
    expansion-generality-synth (ESVar x₁) = SVar x₁
    expansion-generality-synth (ESLam apt ex) with expansion-generality-synth ex
    ... | ih = SLam apt ih
    expansion-generality-synth (ESAp dis _ a x₁ x₂ x₃) = SAp dis a x₁ (expansion-generality-ana x₃)
    expansion-generality-synth ESEHole = SEHole
    expansion-generality-synth (ESNEHole dis ex) = SNEHole (expand-disjoint-new-synth ex dis) (expansion-generality-synth ex)
    expansion-generality-synth (ESAsc x) = SAsc (expansion-generality-ana x)

    expansion-generality-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : ihexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          Γ ⊢ e <= τ
    expansion-generality-ana (EALam apt m ex) = ALam apt m (expansion-generality-ana ex)
    expansion-generality-ana (EASubsume x x₁ x₂ x₃) = ASubsume (expansion-generality-synth x₂) x₃
    expansion-generality-ana EAEHole = ASubsume SEHole TCHole1
    expansion-generality-ana (EANEHole dis x) = ASubsume (SNEHole (expand-disjoint-new-synth x dis) (expansion-generality-synth x)) TCHole1
