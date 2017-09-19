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
  preservation (TALam wt) (Step x₁ x₂ x₃) = {!!}
  preservation (TAAp wt x wt₁) step = {!!}
  preservation (TAEHole x x₁) (Step x₂ x₃ x₄) = {!!}
  preservation (TANEHole x wt x₁) step = {!!}
  preservation (TACast wt x) step = {!!}
