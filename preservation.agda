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
  preservation (TAVar x₁) step = abort (somenotnone (! x₁))
  preservation (TALam wt) (Step x₂ (ITLam x₃) x₄) = TALam wt
  preservation (TALam wt) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = TALam wt
  preservation (TAAp wt x₁ wt₁) (Step x₂ (ITLam x₃) x₄) = TAAp wt x₁ wt₁
  preservation (TAAp wt x wt₁) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = TAAp wt x wt₁
  preservation (TAEHole x x₁) (Step x₂ x₃ x₄) = TAEHole x x₁
  preservation (TANEHole x₁ wt x₂) (Step x₃ (ITLam x₄) x₅) = TANEHole x₁ wt x₂
  preservation (TANEHole x wt x₁) (Step x₂ (ITCast x₃ x₄ x₅) x₆) = TANEHole x wt x₁
  preservation (TACast wt x₁) (Step x₂ (ITLam x₃) x₄) = TACast wt x₁
  preservation (TACast wt x) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = TACast wt x
