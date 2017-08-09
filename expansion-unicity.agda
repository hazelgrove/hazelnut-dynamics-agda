open import Nat
open import Prelude
open import List
open import core
open import contexts
open import correspondence
open import synth-unicity

module expansion-unicity where
  ⦇⦈≠arr : ∀{t1 t2} → t1 ==> t2 == ⦇⦈ → ⊥
  ⦇⦈≠arr ()

  mutual
    expansion-unicity-synth : {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {d1 d2 : dhexp} {Δ1 Δ2 : hctx} →
                            Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
                            Γ ⊢ e ⇒ τ2 ~> d2 ⊣ Δ2 →
                            τ1 == τ2 × d1 == d2 × Δ1 == Δ2
    expansion-unicity-synth ESConst ESConst = refl , refl , refl
    expansion-unicity-synth (ESVar {Γ = Γ} x₁) (ESVar x₂) = ctxunicity {Γ = Γ} x₁ x₂ , refl , refl
    expansion-unicity-synth (ESLam apt1 d1) (ESLam apt2 d2) with expansion-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = ap1 _ ih1  , ap1 _ ih2 , ih3
    expansion-unicity-synth (ESAp1 x₁ x₂ x₃) (ESAp1 x₅ x₆ x₇)
       with expansion-unicity-ana x₃ x₇
    ... | refl , refl , refl
      with expansion-unicity-ana x₂ x₆
    ... | refl , refl , refl = refl , refl , refl
    expansion-unicity-synth (ESAp1 x₁ x₂ x₃) (ESAp2 d5 x₅ x₆) = abort (⦇⦈≠arr (synthunicity (correspondence-synth d5) x₁))
    expansion-unicity-synth (ESAp1 x₁ x₂ x₃) (ESAp3 d5 x₅)    = abort (⦇⦈≠arr (synthunicity (correspondence-synth d5) x₁))
    expansion-unicity-synth (ESAp2 d5 x₁ x₂) (ESAp1 x₄ x₅ x₆) = abort (⦇⦈≠arr (synthunicity (correspondence-synth d5) x₄))
    expansion-unicity-synth (ESAp2 d5 x₁ x₂) (ESAp2 d6 x₄ x₅)
      with expansion-unicity-synth d5 d6 -- | expansion-unicity-ana x₄ x₁
    ... | refl , refl , refl = {!expansion-unicity-ana x₄ x₁!} -- | refl , refl , refl = refl , refl , refl
    expansion-unicity-synth (ESAp2 d5 x₁ x₂) (ESAp3 d6 x₄) = {!!}
    --   with expansion-unicity-synth d5 d6 | expansion-unicity-ana x₄ x₁
    -- ...| refl , refl , refl | refl , refl , refl , refl  = abort (x₂ refl)
    expansion-unicity-synth (ESAp3 d5 x₁) (ESAp1 x₃ x₄ x₅) = abort (⦇⦈≠arr (synthunicity (correspondence-synth d5) x₃))
    expansion-unicity-synth (ESAp3 d5 x₁) (ESAp2 d6 x₃ x₄) = {!!}
    --   with expansion-unicity-synth d5 d6 | expansion-unicity-ana x₃ x₁
    -- ...| refl , refl , refl | refl , refl , refl = abort (x₄ refl)
    expansion-unicity-synth (ESAp3 d5 x₁) (ESAp3 d6 x₃) = {!!}
    --   with expansion-unicity-synth d5 d6 | expansion-unicity-ana x₃ x₁
    -- ... | refl , refl , refl | refl , refl , refl = refl , refl , refl
    expansion-unicity-synth ESEHole ESEHole = refl , refl , refl
    expansion-unicity-synth (ESNEHole d1) (ESNEHole d2) with expansion-unicity-synth d1 d2
    ... | ih1 , ih2 , ih3 = refl , ap1 _ ih2 , ap1 _ ih3
    expansion-unicity-synth (ESAsc1 x x₁) (ESAsc1 x₂ x₃)
      with expansion-unicity-ana x x₂
    ... | refl , refl , refl = refl , refl , refl
    expansion-unicity-synth (ESAsc1 {Γ} {e} {τ} {d} {τ'} x x₁) (ESAsc2 x₂)
      with expansion-unicity-ana x x₂
    ... | refl , contr , refl = abort (x₁ (! contr))
    expansion-unicity-synth (ESAsc2 x) (ESAsc1 x₁ x₂)
      with expansion-unicity-ana x x₁
    ... | refl , contr , refl = abort (x₂ contr)
    expansion-unicity-synth (ESAsc2 x) (ESAsc2 x₁)
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
