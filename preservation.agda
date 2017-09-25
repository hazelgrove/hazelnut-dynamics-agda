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
  preservation TAConst (Step _ _ _) = TAConst
  preservation (TAAp wt x wt₁) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = TAAp wt x wt₁
  preservation (TAAp wt x₁ wt₁) (Step x₂ (ITLam x₃) x₄) = TAAp wt x₁ wt₁
  preservation (TAAp x x₁ x₂) (Step x₃ (ITNEHole x₄) x₅) = TAAp x x₁ x₂
  preservation (TAAp x x₁ x₂) (Step x₃ ITEHole x₅) = TAAp x x₁ x₂
  preservation (TACast wt x) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = TACast wt x
  preservation (TACast wt x₁) (Step x₂ (ITLam x₃) x₄) = TACast wt x₁
  preservation (TACast x x₁) (Step x₂ (ITNEHole x₃) x₄) = TACast x x₁
  preservation (TACast x x₁) (Step x₂ ITEHole x₄) = TACast x x₁
  preservation (TAEHole x x₁) (Step x₂ x₃ x₄) = TAEHole x x₁
  preservation (TALam wt) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = TALam wt
  preservation (TALam wt) (Step x₂ (ITLam x₃) x₄) = TALam wt
  preservation (TALam x₁) (Step x₂ (ITNEHole x₃) x₄) = TALam x₁
  preservation (TALam x₁) (Step x₂ ITEHole x₄) = TALam x₁
  preservation (TANEHole x wt x₁) (Step x₂ (ITCast x₃ x₄ x₅) x₆) = TANEHole x wt x₁
  preservation (TANEHole x x₁ x₂) (Step x₃ (ITNEHole x₄) x₅) = TANEHole x x₁ x₂
  preservation (TANEHole x x₁ x₂) (Step x₃ ITEHole x₅) = TANEHole x x₁ x₂
  preservation (TANEHole x₁ wt x₂) (Step x₃ (ITLam x₄) x₅) = TANEHole x₁ wt x₂
  preservation (TAVar x₁) step = abort (somenotnone (! x₁))
