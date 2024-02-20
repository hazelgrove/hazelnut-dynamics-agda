open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core

module debruijn.debruijn-weakening where

  weakening-wf-var : ∀{Γ τ τ'} →
    Γ ⊢ τ wf →
    (τ' , Γ) ⊢ τ wf
  weakening-wf-var (WFSkipZ wf) = WFSkipZ (weakening-wf-var wf)
  weakening-wf-var WFVarZ = WFSkipZ WFVarZ
  weakening-wf-var (WFSkipS wf) = WFSkipS (weakening-wf-var wf)
  weakening-wf-var (WFVarS wf) = WFSkipS (WFVarS wf)
  weakening-wf-var WFBase = WFBase
  weakening-wf-var WFHole = WFHole
  weakening-wf-var (WFArr wf wf₁) = WFArr (weakening-wf-var wf) (weakening-wf-var wf₁)
  weakening-wf-var (WFForall wf) = {!   !}

  weakening-wf : ∀{Γ τ} →
    Γ ⊢ τ wf →
    (TVar, Γ) ⊢ τ wf
  weakening-wf (WFSkipZ wf) = WFVarZ
  weakening-wf WFVarZ = WFVarZ
  weakening-wf (WFSkipS (WFSkipS wf)) = {!   !}
  weakening-wf (WFSkipS (WFVarS wf)) = WFVarS {! WFSkipS ?  !}
  weakening-wf (WFVarS wf) = WFVarS (weakening-wf wf)
  weakening-wf WFBase = WFBase
  weakening-wf WFHole = WFHole
  weakening-wf (WFArr wf wf₁) = WFArr (weakening-wf wf) (weakening-wf wf₁)
  weakening-wf (WFForall wf) = WFForall (weakening-wf wf)

  -- weakening-varwf : ∀{Γ n} →
  --   Γ ⊢ n varwf →
  --   (TVar, Γ) ⊢ n varwf
  -- weakening-varwf (WFSkip varwf) = WFVarZ
  -- weakening-varwf WFVarZ = WFVarZ
  -- weakening-varwf (WFVarS varwf) = WFVarS (weakening-varwf varwf)

  -- weakening-wf : ∀{Γ τ} →
  --   Γ ⊢ τ wf →
  --   (TVar, Γ) ⊢ τ wf
  -- weakening-wf (WFVar varwf) = WFVar (weakening-varwf varwf)
  -- weakening-wf WFBase = WFBase
  -- weakening-wf WFHole = WFHole
  -- weakening-wf (WFArr wf wf₁) = WFArr (weakening-wf wf) (weakening-wf wf₁)
  -- weakening-wf (WFForall wf) = WFForall (weakening-wf wf)

  -- weakening-n : ∀{Θ τ n} →
  --   Θ ⊢ τ wf →
  --   (n nat+ Θ) ⊢ τ wf
  -- weakening-n {n = Z} wf = wf
  -- weakening-n {n = 1+ n} wf = weakening (weakening-n wf)

  -- weakening-ctx : ∀{Θ Γ} →
  --   ⊢ Γ ctxwf →
  --   1+ Θ ⊢ Γ ctxwf
  -- weakening-ctx CtxWFEmpty = CtxWFEmpty   
  -- weakening-ctx (CtxWFExtend wf ctxwf) = CtxWFExtend (weakening wf) (weakening-ctx ctxwf) 

  -- weakening-wt : ∀{Γ d τ} →
  --   Γ ⊢ d :: τ →
  --   (TVar, Γ) ⊢ d :: τ
  -- weakening-wt TAConst = TAConst
  -- weakening-wt (TAVar x) =  TAVar (InCtxSkip x)
  -- weakening-wt (TALam x wt) = TALam (weakening-wf x) {!   !}
  -- weakening-wt (TATLam wt) = TATLam (weakening-wt wt)
  -- weakening-wt (TAAp wt wt₁) = TAAp (weakening-wt wt) (weakening-wt wt₁)
  -- weakening-wt (TATAp x wt x₁) = TATAp (weakening-wf x) (weakening-wt wt) x₁
  -- weakening-wt (TAEHole x) = TAEHole (weakening-wf x)
  -- weakening-wt (TANEHole x wt) = TANEHole (weakening-wf x) (weakening-wt wt)
  -- weakening-wt (TACast wt x x₁) = TACast (weakening-wt wt) (weakening-wf x) x₁
  -- weakening-wt (TAFailedCast wt x x₁ x₂) = TAFailedCast (weakening-wt wt) x x₁ x₂

  -- weakening-wt-n : ∀{Θ Γ d τ n} →
  --   Θ , Γ ⊢ d :: τ →
  --   (n nat+ Θ) , Γ ⊢ d :: τ
  -- weakening-wt-n {n = Z} wt = wt
  -- weakening-wt-n {n = 1+ n} wt = weakening-wt (weakening-wt-n wt)

  -- strengthen-var : ∀{Θ n} → 
  --   (Θ ≠ 1+ n) → 
  --   (Θ ⊢ T n wf) → 
  --   Θ ⊢ T (1+ n) wf
  -- strengthen-var {Θ = 1+ Z} neq WFVarZ = abort (neq refl)
  -- strengthen-var {Θ = 1+ (1+ Θ)} neq WFVarZ = WFVarS WFVarZ
  -- strengthen-var {Θ = 1+ Z} neq (WFVarS ())
  -- strengthen-var {Θ = 1+ (1+ Θ)} neq (WFVarS {n = n} wf) = WFVarS (strengthen-var h1 wf) 
  --   where 
  --       h1 : 1+ Θ ≠ 1+ n
  --       h1 eq with (sym eq) 
  --       ... | refl = neq refl
