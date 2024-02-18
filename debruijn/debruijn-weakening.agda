open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core

module debruijn.debruijn-weakening where

  weakening : ∀{Θ τ} →
    Θ ⊢ τ wf →
    1+ Θ ⊢ τ wf
  weakening WFVarZ = WFVarZ
  weakening (WFVarS wf) = WFVarS (weakening wf)
  weakening WFBase = WFBase
  weakening WFHole = WFHole 
  weakening (WFArr wf wf₁) = WFArr (weakening wf) (weakening wf₁)
  weakening (WFForall wf) = WFForall (weakening wf) 

  weakening-n : ∀{Θ τ n} →
    Θ ⊢ τ wf →
    (n nat+ Θ) ⊢ τ wf
  weakening-n {n = Z} wf = wf
  weakening-n {n = 1+ n} wf = weakening (weakening-n wf)

  weakening-ctx : ∀{Θ Γ} →
    Θ ⊢ Γ ctxwf →
    1+ Θ ⊢ Γ ctxwf
  weakening-ctx CtxWFEmpty = CtxWFEmpty   
  weakening-ctx (CtxWFExtend wf ctxwf) = CtxWFExtend (weakening wf) (weakening-ctx ctxwf) 

  weakening-wt : ∀{Θ Γ d τ} →
    Θ , Γ ⊢ d :: τ →
    1+ Θ , Γ ⊢ d :: τ
  weakening-wt TAConst = TAConst
  weakening-wt (TAVar x) = TAVar x
  weakening-wt (TALam x wt) = TALam (weakening x) (weakening-wt wt)
  weakening-wt (TATLam wt) = TATLam (weakening-wt wt)
  weakening-wt (TAAp wt wt₁) = TAAp (weakening-wt wt) (weakening-wt wt₁)
  weakening-wt (TATAp x wt x₁) = TATAp (weakening x) (weakening-wt wt) x₁
  weakening-wt (TAEHole x) = TAEHole (weakening x)
  weakening-wt (TANEHole x wt) = TANEHole (weakening x) (weakening-wt wt)
  weakening-wt (TACast wt x x₁) = TACast (weakening-wt wt) (weakening x) x₁
  weakening-wt (TAFailedCast wt x x₁ x₂) = TAFailedCast (weakening-wt wt) x x₁ x₂

  weakening-wt-n : ∀{Θ Γ d τ n} →
    Θ , Γ ⊢ d :: τ →
    (n nat+ Θ) , Γ ⊢ d :: τ
  weakening-wt-n {n = Z} wt = wt
  weakening-wt-n {n = 1+ n} wt = weakening-wt (weakening-wt-n wt)

  strengthen-var : ∀{Θ n} → 
    (Θ ≠ 1+ n) → 
    (Θ ⊢ T n wf) → 
    Θ ⊢ T (1+ n) wf
  strengthen-var {Θ = 1+ Z} neq WFVarZ = abort (neq refl)
  strengthen-var {Θ = 1+ (1+ Θ)} neq WFVarZ = WFVarS WFVarZ
  strengthen-var {Θ = 1+ Z} neq (WFVarS ())
  strengthen-var {Θ = 1+ (1+ Θ)} neq (WFVarS {n = n} wf) = WFVarS (strengthen-var h1 wf) 
    where 
        h1 : 1+ Θ ≠ 1+ n
        h1 eq with (sym eq) 
        ... | refl = neq refl
