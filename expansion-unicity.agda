open import Nat
open import Prelude
open import List
open import core
open import contexts

module expansion-unicity where
  mutual
    expansion-unicity-synth : {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {d1 d2 : dhexp} {Δ1 Δ2 : hctx} →
                            Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
                            Γ ⊢ e ⇒ τ2 ~> d2 ⊣ Δ2 →
                            τ1 == τ2 × d1 == d2 × Δ1 == Δ2
    expansion-unicity-synth ESConst ESConst = refl , refl , refl
    expansion-unicity-synth (ESVar {Γ = Γ} x₁) (ESVar x₂) = ctxunicity {Γ = Γ} x₁ x₂ , refl , refl
    expansion-unicity-synth (ESLam apt1 d1) (ESLam apt2 d2) with expansion-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = ap1 _ ih1  , ap1 _ ih2 , {!!}
    expansion-unicity-synth (ESAp1 x x₁ x₂ x₃) (ESAp1 x₄ x₅ x₆ x₇) = {!!}
    expansion-unicity-synth (ESAp1 x x₁ x₂ x₃) (ESAp2 x₄ d5 x₅ x₆) = {!!}
    expansion-unicity-synth (ESAp1 x x₁ x₂ x₃) (ESAp3 x₄ d5 x₅) = {!!}
    expansion-unicity-synth (ESAp2 x d5 x₁ x₂) (ESAp1 x₃ x₄ x₅ x₆) = {!!}
    expansion-unicity-synth (ESAp2 x d5 x₁ x₂) (ESAp2 x₃ d6 x₄ x₅) = {!!}
    expansion-unicity-synth (ESAp2 x d5 x₁ x₂) (ESAp3 x₃ d6 x₄) = {!!}
    expansion-unicity-synth (ESAp3 x d5 x₁) (ESAp1 x₂ x₃ x₄ x₅) = {!!}
    expansion-unicity-synth (ESAp3 x d5 x₁) (ESAp2 x₂ d6 x₃ x₄) = {!!}
    expansion-unicity-synth (ESAp3 x d5 x₁) (ESAp3 x₂ d6 x₃) = {!!}
    expansion-unicity-synth ESEHole ESEHole = refl , refl , refl
    expansion-unicity-synth (ESNEHole d1) (ESNEHole d2) with expansion-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = refl , ap1 _ ih2 , ap1 _ ih3
    expansion-unicity-synth (ESAsc1 x x₁) (ESAsc1 x₂ x₃) = {!!}
    expansion-unicity-synth (ESAsc1 x x₁) (ESAsc2 x₂) = {!!}
    expansion-unicity-synth (ESAsc2 x) (ESAsc1 x₁ x₂) = {!!}
    expansion-unicity-synth (ESAsc2 x) (ESAsc2 x₁) = {!!}

    expansion-unicity-ana : {Γ : tctx} {e : hexp} {τ1 τ1' τ2 τ2' : htyp} {d1 d2 : dhexp} {Δ1 Δ2 : hctx} →
                          Γ ⊢ e ⇐ τ1 ~> d1 :: τ1' ⊣ Δ1 →
                          Γ ⊢ e ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
                          τ1 == τ2 × d1 == d2 × τ1' == τ2' × Δ1 == Δ2
    expansion-unicity-ana (EALam apt1 d1) (EALam apt2 d2) = {!!}
    expansion-unicity-ana (EALam apt1 d1) (EASubsume x₁ x₂ x₃ x₄) = {!!}
    expansion-unicity-ana (EASubsume x₁ x₂ x₃ x₄) (EALam apt2 d2) = {!!}
    expansion-unicity-ana (EASubsume x x₁ x₂ x₃) (EASubsume x₄ x₅ x₆ x₇) = {!!}
    expansion-unicity-ana (EASubsume x x₁ x₂ x₃) EAEHole = {!!}
    expansion-unicity-ana (EASubsume x x₁ x₂ x₃) (EANEHole x₄) = {!!}
    expansion-unicity-ana EAEHole (EASubsume x x₁ x₂ x₃) = {!!}
    expansion-unicity-ana EAEHole EAEHole = {!!}
    expansion-unicity-ana (EANEHole x) (EASubsume x₂ x₃ x₄ x₅) = {!!}
    expansion-unicity-ana (EANEHole x) (EANEHole x₁) = {!!}
    expansion-unicity-ana (EALam x₁ x₂) (EALamHole x₃ y) = {!!}
    expansion-unicity-ana (EALamHole x₁ x₂) (EALam x₃ y) = {!!}
    expansion-unicity-ana (EALamHole x₁ x₂) (EALamHole x₃ y) = {!!}
    expansion-unicity-ana (EALamHole x₁ x₂) (EASubsume x₃ x₄ x₅ x₆) = {!!}
    expansion-unicity-ana (EASubsume x₁ x₂ x₃ x₄) (EALamHole x₅ y) = {!!}
