open import Nat
open import Prelude
open import List
open import core
open import contexts

module preservation where
  preservation : {Δ : hctx} {d d' : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             Δ ⊢ d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  -- constant cases: constants are values and do not step
  preservation TAConst (Step () (ITLam x₂) x₃)
  preservation TAConst (Step () (ITCast x₁ x₂ x₃) x₄)
  preservation TAConst (Step () ITEHole x₂)
  preservation TAConst (Step () (ITNEHole x₁) x₂)

  -- var case: vars do not step
  preservation (TAVar x₁) _ = abort (somenotnone (! x₁))

  -- lambda cases: lambdas are values and do not step
  preservation (TALam D) (Step () (ITLam x₃) x₄)
  preservation (TALam D) (Step () (ITCast x₂ x₃ x₄) x₅)
  preservation (TALam D) (Step () ITEHole x₃)
  preservation (TALam D) (Step () (ITNEHole x₂) x₃)

  -- ap cases
  preservation (TAAp D x₁ D₁) (Step x₂ (ITLam x₃) x₄) = {!!}
  preservation (TAAp D x D₁) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = {!!}
  preservation (TAAp D x D₁) (Step x₁ ITEHole x₃) = {!!}
  preservation (TAAp D x D₁) (Step x₁ (ITNEHole x₂) x₃) = {!!}

  -- hole cases
  preservation (TAEHole x₁ x₂) (Step () (ITLam x₄) x₅)
  preservation (TAEHole x x₁) (Step () (ITCast x₃ x₄ x₅) x₆)
  preservation (TAEHole x x₁) (Step FHEHole ITEHole FHEHole) = TAEHole x x₁
  preservation (TAEHole x x₁) (Step () (ITNEHole x₃) x₄)

  -- non-empty hole cases
  preservation (TANEHole x₁ D x₂) (Step (FHNEHoleInside x₃) (ITLam x₄) (FHNEHoleInside x₅)) = {!!}
  preservation (TANEHole x D x₁) (Step (FHNEHoleInside x₂) (ITCast x₃ x₄ x₅) (FHNEHoleInside x₆)) = {!!}
  preservation (TANEHole x D x₁) (Step (FHNEHoleInside x₂) ITEHole (FHNEHoleInside x₄)) = {!!}
  preservation (TANEHole x D x₁) (Step (FHNEHoleInside x₂) (ITNEHole x₃) (FHNEHoleInside x₄)) = {!!}
  preservation (TANEHole x D x₁) (Step (FHNEHoleFinal x₂) (ITNEHole x₃) FHNEHoleEvaled) = TANEHole x D x₁

  -- cast cases
  preservation (TACast D x₁) (Step (FHCast x₂) (ITLam x₃) x₄) = {!!}
  preservation (TACast D x) (Step (FHCast x₁) (ITCast x₂ x₃ x₄) x₅) = {!!}
  preservation (TACast D x) (Step (FHCast x₁) ITEHole x₃) = {!!}
  preservation (TACast D x) (Step (FHCast x₁) (ITNEHole x₂) x₃) = {!!}
