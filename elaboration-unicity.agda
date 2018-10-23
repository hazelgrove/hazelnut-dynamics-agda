open import Nat
open import Prelude
open import core
open import contexts
open import synth-unicity
open import lemmas-matching

module elaboration-unicity where
  mutual
    elaboration-unicity-synth : {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {d1 d2 : ihexp} {Δ1 Δ2 : hctx} →
                            Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
                            Γ ⊢ e ⇒ τ2 ~> d2 ⊣ Δ2 →
                            τ1 == τ2 × d1 == d2 × Δ1 == Δ2
    elaboration-unicity-synth ESConst ESConst = refl , refl , refl
    elaboration-unicity-synth (ESVar {Γ = Γ} x₁) (ESVar x₂) = ctxunicity {Γ = Γ} x₁ x₂ , refl , refl
    elaboration-unicity-synth (ESLam apt1 d1) (ESLam apt2 d2)
      with elaboration-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = ap1 _ ih1  , ap1 _ ih2 , ih3
    elaboration-unicity-synth (ESAp _ _ x x₁ x₂ x₃) (ESAp _ _ x₄ x₅ x₆ x₇)
      with synthunicity x x₄
    ... | refl with match-unicity x₁ x₅
    ... | refl with elaboration-unicity-ana x₂ x₆
    ... | refl , refl , refl with elaboration-unicity-ana x₃ x₇
    ... | refl , refl , refl = refl , refl , refl
    elaboration-unicity-synth ESEHole ESEHole = refl , refl , refl
    elaboration-unicity-synth (ESNEHole _ d1) (ESNEHole _ d2)
      with elaboration-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = refl , ap1 _ ih2 , ap1 _ ih3
    elaboration-unicity-synth (ESAsc x) (ESAsc x₁)
      with elaboration-unicity-ana x x₁
    ... | refl , refl , refl = refl , refl , refl

    elaboration-unicity-ana : {Γ : tctx} {e : hexp} {τ τ1 τ2 : htyp} {d1 d2 : ihexp} {Δ1 Δ2 : hctx} →
                          Γ ⊢ e ⇐ τ ~> d1 :: τ1 ⊣ Δ1  →
                          Γ ⊢ e ⇐ τ ~> d2 :: τ2 ⊣ Δ2 →
                          d1 == d2 × τ1 == τ2 × Δ1 == Δ2
    elaboration-unicity-ana (EALam x₁ m D1) (EALam x₂ m2 D2)
      with match-unicity m m2
    ... | refl with elaboration-unicity-ana D1 D2
    ... | refl , refl , refl = refl , refl , refl
    elaboration-unicity-ana (EALam x₁ m D1) (EASubsume x₂ x₃ () x₅)
    elaboration-unicity-ana (EASubsume x₁ x₂ () x₄) (EALam x₅ m D2)
    elaboration-unicity-ana (EASubsume x x₁ x₂ x₃) (EASubsume x₄ x₅ x₆ x₇)
      with elaboration-unicity-synth x₂ x₆
    ... | refl , refl , refl = refl , refl , refl
    elaboration-unicity-ana (EASubsume x x₁ x₂ x₃) EAEHole = abort (x _ refl)
    elaboration-unicity-ana (EASubsume x x₁ x₂ x₃) (EANEHole _ x₄) = abort (x₁ _ _ refl)
    elaboration-unicity-ana EAEHole (EASubsume x x₁ x₂ x₃) = abort (x _ refl)
    elaboration-unicity-ana EAEHole EAEHole = refl , refl , refl
    elaboration-unicity-ana (EANEHole _ x) (EASubsume x₁ x₂ x₃ x₄) = abort (x₂ _ _ refl)
    elaboration-unicity-ana (EANEHole _ x) (EANEHole _ x₁)
      with elaboration-unicity-synth x x₁
    ... | refl , refl , refl = refl , refl , refl
