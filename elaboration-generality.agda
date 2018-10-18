open import Nat
open import Prelude
open import core
open import disjointness

module elaboration-generality where
  mutual
    elaboration-generality-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : ihexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Γ ⊢ e => τ
    elaboration-generality-synth ESConst = SConst
    elaboration-generality-synth (ESVar x₁) = SVar x₁
    elaboration-generality-synth (ESLam apt ex) with elaboration-generality-synth ex
    ... | ih = SLam apt ih
    elaboration-generality-synth (ESAp dis _ a x₁ x₂ x₃) = SAp dis a x₁ (elaboration-generality-ana x₃)
    elaboration-generality-synth ESEHole = SEHole
    elaboration-generality-synth (ESNEHole dis ex) = SNEHole (elab-disjoint-new-synth ex dis) (elaboration-generality-synth ex)
    elaboration-generality-synth (ESAsc x) = SAsc (elaboration-generality-ana x)

    elaboration-generality-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : ihexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          Γ ⊢ e <= τ
    elaboration-generality-ana (EALam apt m ex) = ALam apt m (elaboration-generality-ana ex)
    elaboration-generality-ana (EASubsume x x₁ x₂ x₃) = ASubsume (elaboration-generality-synth x₂) x₃
    elaboration-generality-ana EAEHole = ASubsume SEHole TCHole1
    elaboration-generality-ana (EANEHole dis x) = ASubsume (SNEHole (elab-disjoint-new-synth x dis) (elaboration-generality-synth x)) TCHole1
