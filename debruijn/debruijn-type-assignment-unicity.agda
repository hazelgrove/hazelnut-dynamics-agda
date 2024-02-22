open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-meet

module debruijn.debruijn-type-assignment-unicity where

  context-unicity : ∀{Γ n τ τ'} → 
    n , τ ∈ Γ → 
    n , τ' ∈ Γ → 
    τ == τ'
  context-unicity (InCtxSkip inctx1) (InCtxSkip inctx2) rewrite context-unicity inctx1 inctx2 = refl
  context-unicity InCtxZ InCtxZ = refl
  context-unicity (InCtx1+ inctx1) (InCtx1+ inctx2) = context-unicity inctx1 inctx2

  synth-unicity : ∀{Γ d τ' τ} →
    Γ ⊢ d => τ →
    Γ ⊢ d => τ' →
    τ == τ'
  synth-unicity SConst SConst = refl
  synth-unicity (SAsc x x₁) (SAsc x₂ x₃) = refl
  synth-unicity (SVar x) (SVar x₁) = context-unicity x x₁
  synth-unicity (SAp syn1 x x₁) (SAp syn2 x₂ x₃) rewrite synth-unicity syn1 syn2 with ⊓-unicity x x₂
  ... | refl = refl
  synth-unicity SEHole SEHole = refl
  synth-unicity (SNEHole syn1) (SNEHole syn2) = refl
  synth-unicity (SLam x syn1) (SLam x₁ syn2) rewrite synth-unicity syn1 syn2 = refl
  synth-unicity (STLam syn1) (STLam syn2) rewrite synth-unicity syn1 syn2 = refl
  synth-unicity (STAp x syn1 x₁ refl) (STAp x₃ syn2 x₄ refl) rewrite synth-unicity syn1 syn2 with ⊓-unicity x₁ x₄
  ... | refl = refl

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
