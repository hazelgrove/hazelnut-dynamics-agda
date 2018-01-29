open import Nat
open import Prelude
open import List
open import core
open import contexts
open import correspondence
open import synth-unicity
open import lemmas-matching

module expansion-unicity where
  -- todo: move to a lemmas file
  ⦇⦈≠arr : ∀{t1 t2} → t1 ==> t2 == ⦇⦈ → ⊥
  ⦇⦈≠arr ()

  mutual
    expansion-unicity-synth : {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {d1 d2 : dhexp} {Δ1 Δ2 : hctx} →
                            Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
                            Γ ⊢ e ⇒ τ2 ~> d2 ⊣ Δ2 →
                            τ1 == τ2 × d1 == d2 × Δ1 == Δ2
    expansion-unicity-synth ESConst ESConst = refl , refl , refl
    expansion-unicity-synth (ESVar {Γ = Γ} x₁) (ESVar x₂) = ctxunicity {Γ = Γ} x₁ x₂ , refl , refl
    expansion-unicity-synth (ESLam apt1 d1) (ESLam apt2 d2)
      with expansion-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = ap1 _ ih1  , ap1 _ ih2 , ih3
    expansion-unicity-synth (ESAp x x₁ x₂ x₃) (ESAp x₄ x₅ x₆ x₇)
      with synthunicity x x₄
    ... | refl with match-unicity x₁ x₅
    ... | refl with expansion-unicity-ana x₂ x₆
    ... | refl , refl , refl with expansion-unicity-ana x₃ x₇
    ... | refl , refl , refl = refl , refl , refl
    expansion-unicity-synth ESEHole ESEHole = refl , refl , refl
    expansion-unicity-synth (ESNEHole d1) (ESNEHole d2)
      with expansion-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = refl , ap1 _ ih2 , ap1 _ ih3
    expansion-unicity-synth (ESAsc x) (ESAsc x₁)
      with expansion-unicity-ana x x₁
    ... | refl , refl , refl = refl , refl , refl

    expansion-unicity-ana : {Γ : tctx} {e : hexp} {τ1 τ2 τ2' : htyp} {d d' : dhexp} {Δ Δ' : hctx} →
                          Γ ⊢ e ⇐ τ1 ~> d  :: τ2  ⊣ Δ  →
                          Γ ⊢ e ⇐ τ1 ~> d' :: τ2' ⊣ Δ' →
                          d == d' × τ2 == τ2' × Δ == Δ'
    expansion-unicity-ana (EALam x₁ D1) (EALam x₂ D2)
      with expansion-unicity-ana D1 D2
    ... | refl , refl , refl = refl , refl , refl
    expansion-unicity-ana (EALam x₁ D1) (EASubsume x₂ x₃ () x₅)
    expansion-unicity-ana (EALamHole x₁ D1) (EALamHole x₂ D2)
      with expansion-unicity-ana D1 D2
    ... | refl , refl , refl = refl , refl , refl
    expansion-unicity-ana (EALamHole x₁ D1) (EASubsume x₂ x₃ () x₅)
    expansion-unicity-ana (EASubsume x₁ x₂ () x₄) (EALam x₅ D2)
    expansion-unicity-ana (EASubsume x₁ x₂ () x₄) (EALamHole x₅ D2)
    expansion-unicity-ana (EASubsume x x₁ x₂ x₃) (EASubsume x₄ x₅ x₆ x₇)
      with expansion-unicity-synth x₂ x₆
    ... | refl , refl , refl = refl , refl , refl
    expansion-unicity-ana (EASubsume x x₁ x₂ x₃) EAEHole = abort (x _ refl)
    expansion-unicity-ana (EASubsume x x₁ x₂ x₃) (EANEHole x₄) = abort (x₁ _ _ refl)
    expansion-unicity-ana EAEHole (EASubsume x x₁ x₂ x₃) = abort (x _ refl)
    expansion-unicity-ana EAEHole EAEHole = refl , refl , refl
    expansion-unicity-ana (EANEHole x) (EASubsume x₁ x₂ x₃ x₄) = abort (x₂ _ _ refl)
    expansion-unicity-ana (EANEHole x) (EANEHole x₁)
      with expansion-unicity-synth x x₁
    ... | refl , refl , refl = refl , refl , refl
