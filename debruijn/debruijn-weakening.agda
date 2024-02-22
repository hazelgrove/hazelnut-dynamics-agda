open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core

module debruijn.debruijn-weakening where

  weakening-wf-var-n : ∀{Γ n τ τ'} →
    ctx-extend-tvars n Γ ⊢ τ wf →
    ctx-extend-tvars n (τ' , Γ) ⊢ τ wf
  weakening-wf-var-n {n = Z} (WFSkip wf) = WFSkip (WFSkip wf)
  weakening-wf-var-n {n = Z} WFVarZ = WFSkip WFVarZ
  weakening-wf-var-n {n = Z} (WFVarS wf) = WFSkip (WFVarS wf)
  weakening-wf-var-n {n = Z} WFBase = WFBase
  weakening-wf-var-n {n = Z} WFHole = WFHole
  weakening-wf-var-n {n = Z} (WFArr wf wf₁) = WFArr (weakening-wf-var-n wf) (weakening-wf-var-n wf₁)
  weakening-wf-var-n {n = Z} (WFForall wf) = WFForall (weakening-wf-var-n wf)
  weakening-wf-var-n {n = 1+ n} WFVarZ = WFVarZ
  weakening-wf-var-n {n = 1+ n} (WFVarS wf) = WFVarS (weakening-wf-var-n wf)
  weakening-wf-var-n {n = 1+ n} WFBase = WFBase
  weakening-wf-var-n {n = 1+ n} WFHole = WFHole
  weakening-wf-var-n {n = 1+ n} (WFArr wf wf₁) = WFArr (weakening-wf-var-n wf) (weakening-wf-var-n wf₁)
  weakening-wf-var-n {n = 1+ n} (WFForall wf) = WFForall (weakening-wf-var-n wf)

  weakening-wf-var : ∀{Γ τ τ'} →
    Γ ⊢ τ wf →
    (τ' , Γ) ⊢ τ wf
  weakening-wf-var = weakening-wf-var-n 

  strengthen-wf-var-n : ∀{Γ n τ τ'} →
    ctx-extend-tvars n (τ' , Γ) ⊢ τ wf →
    ctx-extend-tvars n Γ ⊢ τ wf
  strengthen-wf-var-n {n = Z} (WFSkip wf) = wf
  strengthen-wf-var-n {n = Z} WFBase = WFBase
  strengthen-wf-var-n {n = Z} WFHole = WFHole
  strengthen-wf-var-n {n = Z} (WFArr wf wf₁) = WFArr (strengthen-wf-var-n wf) (strengthen-wf-var-n wf₁)
  strengthen-wf-var-n {n = Z} (WFForall wf) = WFForall (strengthen-wf-var-n wf)
  strengthen-wf-var-n {n = 1+ n} WFVarZ = WFVarZ
  strengthen-wf-var-n {n = 1+ n} (WFVarS wf) = WFVarS (strengthen-wf-var-n wf)
  strengthen-wf-var-n {n = 1+ n} WFBase = WFBase
  strengthen-wf-var-n {n = 1+ n} WFHole = WFHole
  strengthen-wf-var-n {n = 1+ n} (WFArr wf wf₁) = WFArr (strengthen-wf-var-n wf) (strengthen-wf-var-n wf₁)
  strengthen-wf-var-n {n = 1+ n} (WFForall wf) = WFForall (strengthen-wf-var-n wf)

  strengthen-wf-var : ∀{Γ τ τ'} →
    (τ' , Γ) ⊢ τ wf →
    Γ ⊢ τ wf
  strengthen-wf-var = strengthen-wf-var-n 

  strengthen-wf-var-reverse-n : ∀{Γ n τ τ'} →
    ctx-extend-tvars n (Γ ctx+ (τ' , ∅)) ⊢ τ wf →
    ctx-extend-tvars n Γ ⊢ τ wf
  strengthen-wf-var-reverse-n {Γ = x , Γ} {n = Z} (WFSkip wf) = WFSkip (strengthen-wf-var-reverse-n {n = Z} wf)
  strengthen-wf-var-reverse-n {Γ = TVar, Γ} {n = Z} (WFVarS wf) = WFVarS (strengthen-wf-var-reverse-n {n = Z} wf)
  strengthen-wf-var-reverse-n {Γ = Γ} {n = 1+ n} (WFVarS wf) = WFVarS (strengthen-wf-var-reverse-n {n = n} wf)
  strengthen-wf-var-reverse-n {n = 1+ n} WFVarZ = WFVarZ
  strengthen-wf-var-reverse-n {Γ = TVar, Γ} {n = Z} WFVarZ = WFVarZ
  strengthen-wf-var-reverse-n WFBase = WFBase
  strengthen-wf-var-reverse-n WFHole = WFHole
  strengthen-wf-var-reverse-n {n = n} (WFArr wf wf₁) = WFArr (strengthen-wf-var-reverse-n {n = n} wf) (strengthen-wf-var-reverse-n {n = n} wf₁)
  strengthen-wf-var-reverse-n {n = n} (WFForall wf) = WFForall (strengthen-wf-var-reverse-n {n = 1+ n} wf)

  strengthen-wf-var-reverse : ∀{Γ τ τ'} →
    (Γ ctx+ (τ' , ∅)) ⊢ τ wf →
    Γ ⊢ τ wf
  strengthen-wf-var-reverse wf = strengthen-wf-var-reverse-n {n = Z} wf
  
  weakening-wf-tvar : ∀{Γ τ} →
    Γ ⊢ τ wf →
    (TVar, Γ) ⊢ τ wf
  weakening-wf-tvar (WFSkip {n = Z} wf) = WFVarZ
  weakening-wf-tvar (WFSkip {x , Γ} {n = 1+ n} (WFSkip wf)) with weakening-wf-tvar wf 
  ... | WFVarS wf' = WFVarS (WFSkip (WFSkip wf'))
  weakening-wf-tvar (WFSkip {TVar, Γ} {n = 1+ n} wf)  with weakening-wf-tvar wf 
  ... | WFVarS wf' = WFVarS (WFSkip wf')
  weakening-wf-tvar WFVarZ = WFVarZ
  weakening-wf-tvar (WFVarS wf) = WFVarS (weakening-wf-tvar wf)
  weakening-wf-tvar WFBase = WFBase
  weakening-wf-tvar WFHole = WFHole
  weakening-wf-tvar (WFArr wf wf₁) = WFArr (weakening-wf-tvar wf) (weakening-wf-tvar wf₁)
  weakening-wf-tvar (WFForall wf) = WFForall (weakening-wf-tvar wf)

  wf-swap-tvar : ∀{Γ τ} → (Γ ctx+ (TVar, ∅)) ⊢ τ wf → (TVar, Γ) ⊢ τ wf
  wf-swap-tvar {∅} WFVarZ = WFVarZ
  wf-swap-tvar WFBase = WFBase
  wf-swap-tvar WFHole = WFHole
  wf-swap-tvar (WFArr wf wf₁) = WFArr (wf-swap-tvar wf) (wf-swap-tvar wf₁)
  wf-swap-tvar (WFForall wf) = WFForall (wf-swap-tvar wf)
  wf-swap-tvar {x , Γ} (WFSkip wf) with wf-swap-tvar wf
  ... | wf' = weakening-wf-var-n wf'
  wf-swap-tvar {TVar, Γ} WFVarZ = WFVarZ
  wf-swap-tvar {TVar, Γ} (WFVarS wf) =  WFVarS (wf-swap-tvar wf)

  weakening-wf : ∀{Γ1 Γ2 τ} → Γ1 ⊢ τ wf → (Γ1 ctx+ Γ2) ⊢ τ wf
  weakening-wf (WFSkip wf) = WFSkip (weakening-wf wf)
  weakening-wf WFVarZ = WFVarZ
  weakening-wf (WFVarS wf) = WFVarS (weakening-wf wf)
  weakening-wf WFBase = WFBase
  weakening-wf WFHole = WFHole
  weakening-wf (WFArr wf wf₁) = WFArr (weakening-wf wf) (weakening-wf wf₁)
  weakening-wf (WFForall wf) = WFForall (weakening-wf wf)

  weakening-inctx : ∀{Γ1 Γ2 n τ} → n , τ ∈ Γ1 → n , τ ∈ (Γ1 ctx+ Γ2)
  weakening-inctx (InCtxSkip inctx) = InCtxSkip (weakening-inctx inctx)
  weakening-inctx InCtxZ = InCtxZ
  weakening-inctx (InCtx1+ inctx) = InCtx1+ (weakening-inctx inctx)

  weakening-wt : ∀{Γ1 Γ2 d τ} → Γ1 ⊢ d :: τ → (Γ1 ctx+ Γ2) ⊢ d :: τ
  weakening-wt TAConst = TAConst
  weakening-wt (TAVar x) = TAVar (weakening-inctx x)
  weakening-wt (TALam x wt) = TALam (weakening-wf x) (weakening-wt wt)
  weakening-wt (TATLam wt) = TATLam (weakening-wt wt)
  weakening-wt (TAAp wt wt₁) = TAAp (weakening-wt wt) (weakening-wt wt₁)
  weakening-wt (TATAp x wt x₁) = TATAp (weakening-wf x) (weakening-wt wt) x₁
  weakening-wt TAEHole = TAEHole
  weakening-wt (TANEHole wt) = TANEHole (weakening-wt wt)
  weakening-wt (TACast wt x x₁) = TACast (weakening-wt wt) (weakening-wf x) x₁
  weakening-wt (TAFailedCast wt x x₁ x₂) = TAFailedCast (weakening-wt wt) x x₁ x₂

  -- weakening-varwf : ∀{Γ n} →
  --   Γ ⊢ n varwf →
  --   (TVar, Γ) ⊢ n varwf
  -- weakening-varwf (WFSkip varwf) = WFVarZ
  -- weakening-varwf WFVarZ = WFVarZ
  -- weakening-varwf (WFVarS varwf) = WFVarS (weakening-varwf varwf)

  -- weakening-wf-tvar : ∀{Γ τ} →
  --   Γ ⊢ τ wf →
  --   (TVar, Γ) ⊢ τ wf
  -- weakening-wf-tvar (WFVar varwf) = WFVar (weakening-varwf varwf)
  -- weakening-wf-tvar WFBase = WFBase
  -- weakening-wf-tvar WFHole = WFHole
  -- weakening-wf-tvar (WFArr wf wf₁) = WFArr (weakening-wf-tvar wf) (weakening-wf-tvar wf₁)
  -- weakening-wf-tvar (WFForall wf) = WFForall (weakening-wf-tvar wf)

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
  -- weakening-wt (TALam x wt) = TALam (weakening-wf-tvar x) {!   !}
  -- weakening-wt (TATLam wt) = TATLam (weakening-wt wt)
  -- weakening-wt (TAAp wt wt₁) = TAAp (weakening-wt wt) (weakening-wt wt₁)
  -- weakening-wt (TATAp x wt x₁) = TATAp (weakening-wf-tvar x) (weakening-wt wt) x₁
  -- weakening-wt (TAEHole x) = TAEHole (weakening-wf-tvar x)
  -- weakening-wt (TANEHole x wt) = TANEHole (weakening-wf-tvar x) (weakening-wt wt)
  -- weakening-wt (TACast wt x x₁) = TACast (weakening-wt wt) (weakening-wf-tvar x) x₁
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
 