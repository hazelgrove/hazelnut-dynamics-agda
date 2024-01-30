open import Nat
open import Prelude
open import core
open import contexts
open import synth-unicity
open import lemmas-matching

module elaboration-unicity where
  mutual

    elabortation-unicity-compatible : ∀{Γ e τ τ1 τ2 d1 d2 Δ1 Δ2 Θ} →
                                  ((u : Nat) → e ≠ ⦇-⦈[ u ]) →
                                  ((e' : hexp) (u : Nat) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
                                  Θ , Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
                                  Θ , Γ ⊢ e ⇐ τ ~> d2 :: τ2 ⊣ Δ2 → 
                                  τ1 == τ2 × d1 == d2 × Δ1 == Δ2
    elabortation-unicity-compatible neq1 _ (ESEHole {u = u}) EAEHole = abort (neq1 u refl)
    elabortation-unicity-compatible {e = e} _ neq2 x (EANEHole {e = e₁} {u = u} x₁ x₂) = abort (neq2 e₁ u refl)
    elabortation-unicity-compatible _ _ D1 (EASubsume x x₁ D2 x₃) = elaboration-unicity-synth D1 D2
    elabortation-unicity-compatible _ _ (ESTLam D1) (EATLam neq1 neq2 m D2) 
      with elabortation-unicity-compatible neq1 neq2 D1 D2 
    ... | refl , refl , refl = refl , refl , refl

    elaboration-unicity-synth : ∀{Γ e τ1 τ2 d1 d2 Δ1 Δ2 Θ} →
                            Θ , Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
                            Θ , Γ ⊢ e ⇒ τ2 ~> d2 ⊣ Δ2 →
                            τ1 == τ2 × d1 == d2 × Δ1 == Δ2
    elaboration-unicity-synth ESConst ESConst = refl , refl , refl
    elaboration-unicity-synth (ESVar {Γ = Γ} x₁) (ESVar x₂) = ctxunicity {Γ = Γ} x₁ x₂ , refl , refl
    elaboration-unicity-synth (ESLam apt1 wf1 d1) (ESLam apt2 wf2 d2)
      with elaboration-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = ap1 _ ih1  , ap1 _ ih2 , ih3
    elaboration-unicity-synth (ESTLam d1) (ESTLam d2)
      with elaboration-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 rewrite ih1 | ih2 = refl , refl , ih3
    elaboration-unicity-synth (ESAp _ _ x x₁ x₂ x₃) (ESAp _ _ x₄ x₅ x₆ x₇)
      with synthunicity x x₄
    ... | refl with match-unicity x₁ x₅
    ... | refl with elaboration-unicity-ana x₂ x₆
    ... | refl , refl , refl with elaboration-unicity-ana x₃ x₇
    ... | refl , refl , refl = refl , refl , refl
    elaboration-unicity-synth (ESTAp wf1 x1 m1 d1 eq1) (ESTAp wf2 x2 m2 d2 eq2)
      with synthunicity x1 x2 
    ... | refl with forall-match-unicity m1 m2
    ... | refl with elaboration-unicity-ana d1 d2 
    ... | refl , refl , refl rewrite (sym eq1) = eq2 , refl , refl
    elaboration-unicity-synth ESEHole ESEHole = refl , refl , refl
    elaboration-unicity-synth (ESNEHole _ d1) (ESNEHole _ d2)
      with elaboration-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = refl , ap1 _ ih2 , ap1 _ ih3
    elaboration-unicity-synth (ESAsc wf1 x) (ESAsc wf2 x₁)
      with elaboration-unicity-ana x x₁
    ... | refl , refl , refl = refl , refl , refl

    elaboration-unicity-ana : ∀{Γ e τ τ1 τ2 d1 d2 Δ1 Δ2 Θ}  →
                          Θ , Γ ⊢ e ⇐ τ ~> d1 :: τ1 ⊣ Δ1  →
                          Θ , Γ ⊢ e ⇐ τ ~> d2 :: τ2 ⊣ Δ2 →
                          d1 == d2 × τ1 == τ2 × Δ1 == Δ2
    elaboration-unicity-ana (EALam x₁ m D1) (EALam x₂ m2 D2)
      with match-unicity m m2
    ... | refl with elaboration-unicity-ana D1 D2
    ... | refl , refl , refl = refl , refl , refl
    elaboration-unicity-ana (EATLam _ _ m D1) (EATLam _ _ m2 D2)
      with forall-match-unicity m m2
    ... | refl with elaboration-unicity-ana D1 D2
    ... | refl , refl , refl = refl , refl , refl
    elaboration-unicity-ana (EALam x₁ m D1) (EASubsume x₂ x₃ () x₅)
    elaboration-unicity-ana (EASubsume x₁ x₂ () x₄) (EALam x₅ m D2)
    elaboration-unicity-ana (EATLam neq1 neq2 m D1) (EASubsume x x₁ (ESTLam D2) x₄) 
      with (elabortation-unicity-compatible neq1 neq2 D2 D1) 
    ... | refl , refl , refl = refl , refl , refl
    elaboration-unicity-ana (EASubsume x x₁ (ESTLam D2) x₄) (EATLam neq1 neq2 m D1)
      with (elabortation-unicity-compatible neq1 neq2 D2 D1) 
    ... | refl , refl , refl = refl , refl , refl
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
