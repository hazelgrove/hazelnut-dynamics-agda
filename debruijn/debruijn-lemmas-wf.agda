open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-subst
open import debruijn.debruijn-core
open import debruijn.debruijn-weakening
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-subst

module debruijn.debruijn-lemmas-wf where

  wf-inc : ∀{Γ τ m} → Γ ⊢ τ wf → (TVar, Γ) ⊢ ↑ m 1 τ wf
  wf-inc {m = m} (WFSkip wf) = weakening-wf-var-n (wf-inc {m = m} wf)
  wf-inc {m = Z} WFVarZ = WFVarS WFVarZ
  wf-inc {m = 1+ m} WFVarZ = WFVarZ
  wf-inc {m = Z} (WFVarS wf) = WFVarS (WFVarS wf)
  wf-inc {m = 1+ m} (WFVarS wf) = WFVarS (wf-inc {m = m} wf)
  wf-inc WFBase = WFBase
  wf-inc WFHole = WFHole
  wf-inc (WFArr wf wf₁) = WFArr (wf-inc wf) (wf-inc wf₁)
  wf-inc (WFForall wf) = WFForall (wf-inc wf)

  wf-ctx-var : ∀{τ n Γ} →
    ⊢ Γ ctxwf →
    n , τ ∈ Γ → 
    Γ ⊢ τ wf
  wf-ctx-var CtxWFEmpty ()
  wf-ctx-var (CtxWFVar x ctxwf) InCtxZ = weakening-wf-var x
  wf-ctx-var (CtxWFVar x ctxwf) (InCtx1+ inctx) = weakening-wf-var (wf-ctx-var ctxwf inctx)
  wf-ctx-var (CtxWFTVar ctxwf) (InCtxSkip inctx) = wf-inc (wf-ctx-var ctxwf inctx)
  
  wf-⊑t : ∀{Γ1 Γ2 τ1 τ2} → Γ1 ⊢ τ1 wf → Γ1 ⊑c Γ2 → τ1 ⊑t τ2 → Γ2 ⊢ τ2 wf
  wf-⊑t wf precc PTBase = WFBase 
  wf-⊑t _ precc PTHole = WFHole
  wf-⊑t (WFArr wf1 wf2) precc (PTArr prec1 prec2) = WFArr (wf-⊑t wf1 precc prec1) (wf-⊑t wf2 precc prec2)
  wf-⊑t (WFForall wf) precc (PTForall prec) = WFForall (wf-⊑t wf (PCTVar precc) prec)
  wf-⊑t (WFSkip wf) (PCVar x precc) PTTVar = WFSkip (wf-⊑t wf precc PTTVar)
  wf-⊑t WFVarZ (PCTVar precc) PTTVar = WFVarZ
  wf-⊑t (WFVarS wf) (PCTVar precc) PTTVar = WFVarS (wf-⊑t wf precc PTTVar)

  wf-⊓ : ∀{τ1 τ2 τ3 Γ} → τ1 ⊓ τ2 == τ3 → Γ ⊢ τ1 wf → Γ ⊢ τ2 wf → Γ ⊢ τ3 wf
  wf-⊓ MeetHoleL wf1 wf2 = wf2 
  wf-⊓ MeetHoleR wf1 wf2 = wf1
  wf-⊓ MeetBase wf1 wf2 = wf2
  wf-⊓ MeetVar wf1 wf2 = wf2
  wf-⊓ (MeetArr meet meet₁) (WFArr wf1 wf2) (WFArr wf3 wf4) = WFArr (wf-⊓ meet wf1 wf3) (wf-⊓ meet₁ wf2 wf4)
  wf-⊓ (MeetForall meet) (WFForall wf1) (WFForall wf2) = WFForall (wf-⊓ meet wf1 wf2)

  wf-gnd : ∀{Γ τ} → τ ground → Γ ⊢ τ wf
  wf-gnd GBase = WFBase
  wf-gnd GArr = WFArr WFHole WFHole
  wf-gnd GForall = WFForall WFHole

  wf-syn : ∀{τ e Γ} → 
    ⊢ Γ ctxwf → 
    Γ ⊢ e => τ → 
    Γ ⊢ τ wf
  wf-syn ctxwf SConst = WFBase
  wf-syn ctxwf (SAsc x x₁) = x
  wf-syn ctxwf (SVar x) = wf-ctx-var ctxwf x
  wf-syn ctxwf (SAp syn meet _) with wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
  ... | WFArr _ wf = wf
  wf-syn ctxwf SEHole = WFHole
  wf-syn ctxwf (SNEHole syn) = WFHole
  wf-syn ctxwf (SLam x syn) = WFArr x (strengthen-wf-var (wf-syn (CtxWFVar x ctxwf) syn))
  wf-syn ctxwf (STLam syn) = WFForall (wf-syn (CtxWFTVar ctxwf) syn)
  wf-syn ctxwf (STAp wf syn meet refl) with wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole) 
  ... | WFForall wf' = wf-TTSub wf wf'
  
  wf-elab-syn : ∀{τ e d Γ} → 
    ⊢ Γ ctxwf → 
    Γ ⊢ e ⇒ τ ~> d → 
    Γ ⊢ τ wf
  wf-elab-syn ctxwf ESConst = WFBase
  wf-elab-syn ctxwf (ESVar x) = wf-ctx-var ctxwf x
  wf-elab-syn ctxwf (ESLam x syn) = WFArr x (strengthen-wf-var (wf-elab-syn (CtxWFVar x ctxwf) syn))
  wf-elab-syn ctxwf (ESTLam syn) = WFForall (wf-elab-syn (CtxWFTVar ctxwf) syn)
  wf-elab-syn ctxwf (ESAp syn meet _ _) with wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
  ... | WFArr _ wf = wf
  wf-elab-syn ctxwf (ESTAp wf syn meet _ refl) with wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole) 
  ... | WFForall wf' = wf-TTSub wf wf'
  wf-elab-syn ctxwf ESEHole = WFHole
  wf-elab-syn ctxwf (ESNEHole syn) = WFHole
  wf-elab-syn ctxwf (ESAsc x x₁) = x

  wf-ta : ∀{τ d Γ} → 
    ⊢ Γ ctxwf → 
    Γ ⊢ d :: τ → 
    Γ ⊢ τ wf
  wf-ta ctxwf TAConst = WFBase
  wf-ta ctxwf (TAVar x) = wf-ctx-var ctxwf x
  wf-ta ctxwf (TALam x wt) = WFArr x (strengthen-wf-var (wf-ta (CtxWFVar x ctxwf) wt))
  wf-ta ctxwf (TATLam wt) = WFForall (wf-ta (CtxWFTVar ctxwf) wt)
  wf-ta ctxwf (TAAp wt wt₁) with wf-ta ctxwf wt 
  ... | WFArr _ wf = wf
  wf-ta ctxwf (TATAp x wt refl) with wf-ta ctxwf wt 
  ... | WFForall wf = wf-TTSub x wf 
  wf-ta ctxwf (TAEHole wf) = wf 
  wf-ta ctxwf (TANEHole wf _) = wf
  wf-ta ctxwf (TACast _ wf _) = wf 
  wf-ta ctxwf (TAFailedCast wt _ GBase _) = WFBase    
  wf-ta ctxwf (TAFailedCast wt _ GArr _) = WFArr WFHole WFHole
  wf-ta ctxwf (TAFailedCast wt _ GForall _) = WFForall WFHole