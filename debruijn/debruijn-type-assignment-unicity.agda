open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core

module debruijn.debruijn-type-assignment-unicity where

  context-unicity : ∀{Γ n τ τ'} → 
    n , τ ∈ Γ → 
    n , τ' ∈ Γ → 
    τ == τ'
  context-unicity (InCtxSkip inctx1) (InCtxSkip inctx2) rewrite context-unicity inctx1 inctx2 = refl
  context-unicity InCtxZ InCtxZ = refl
  context-unicity (InCtx1+ inctx1) (InCtx1+ inctx2) = context-unicity inctx1 inctx2

  -- type assignment only assigns one type
  type-assignment-unicity : ∀{Γ d τ' τ} →
    Γ ⊢ d :: τ →
    Γ ⊢ d :: τ' →
    τ == τ'
  type-assignment-unicity TAConst TAConst = refl
  type-assignment-unicity (TAVar inctx1) (TAVar inctx2) = context-unicity inctx1 inctx2
  type-assignment-unicity (TALam _ wt1) (TALam _ wt2) rewrite type-assignment-unicity wt1 wt2 = refl
  type-assignment-unicity (TATLam wt1) (TATLam wt2) rewrite type-assignment-unicity wt1 wt2 = refl
  type-assignment-unicity (TAAp wt1 _) (TAAp wt2 _) with type-assignment-unicity wt1 wt2
  ... | refl = refl
  type-assignment-unicity (TATAp _ wt1 eq1) (TATAp _ wt2 eq2) with type-assignment-unicity wt1 wt2
  ... | refl rewrite eq1 = eq2
  type-assignment-unicity (TAEHole _) (TAEHole _) = refl
  type-assignment-unicity (TANEHole _ _) (TANEHole _ _) = refl
  type-assignment-unicity (TACast wt1 _ _) (TACast wt2 _ _) rewrite type-assignment-unicity wt1 wt2 = refl
  type-assignment-unicity (TAFailedCast wt1 _ _ _) (TAFailedCast wt2 _ _ _) rewrite type-assignment-unicity wt1 wt2 = refl
