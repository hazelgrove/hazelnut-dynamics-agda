open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-index
-- open import debruijn.debruijn-lemmas-prec

module debruijn.debruijn-lemmas-wf where

  wf-ctx-var : ∀{τ n Θ Γ} → 
    (Θ ⊢ Γ ctxwf) →
    (n , τ ∈ Γ) → 
    Θ ⊢ τ wf
  wf-ctx-var (CtxWFExtend x ctxwf) InCtxZ = x
  wf-ctx-var (CtxWFExtend x ctxwf) (InCtx1+ inctx) = wf-ctx-var ctxwf inctx

  weakening : ∀{Θ τ} →
    Θ ⊢ τ wf →
    1+ Θ ⊢ τ wf
  weakening WFVarZ = WFVarZ
  weakening (WFVarS wf) = WFVarS (weakening wf)
  weakening WFBase = WFBase
  weakening WFHole = WFHole 
  weakening (WFArr wf wf₁) = WFArr (weakening wf) (weakening wf₁)
  weakening (WFForall wf) = WFForall (weakening wf) 

  weakening-ctx : ∀{Θ Γ} →
    Θ ⊢ Γ ctxwf →
    1+ Θ ⊢ Γ ctxwf
  weakening-ctx CtxWFEmpty = CtxWFEmpty   
  weakening-ctx (CtxWFExtend wf ctxwf) = CtxWFExtend (weakening wf) (weakening-ctx ctxwf) 

  strengthen-var : ∀{Θ n} → 
    (Θ ≠ 1+ n) → 
    (Θ ⊢ T n wf) → 
    Θ ⊢ T (1+ n) wf
  strengthen-var {Θ = 1+ Z} neq WFVarZ = abort (neq refl)
  strengthen-var {Θ = 1+ (1+ Θ)} neq WFVarZ = WFVarS WFVarZ
  strengthen-var {Θ = 1+ Z} neq (WFVarS ())
  strengthen-var {Θ = 1+ (1+ Θ)} neq (WFVarS {m = m} wf) = WFVarS (strengthen-var h1 wf) 
    where 
        h1 : 1+ Θ ≠ 1+ m
        h1 eq with (sym eq) 
        ... | refl = neq refl

  wf-TTSub-helper : ∀{Θ n τ1 τ2} → (Θ ⊢ τ1 wf) → (1+ (Θ nat+ n) ⊢ τ2 wf) → ((Θ nat+ n) ⊢ TT[ τ1 / Θ ] τ2 wf)
  wf-TTSub-helper = {!   !}

  wf-TTSub : ∀{Θ τ1 τ2} → (Θ ⊢ τ1 wf) → (1+ Θ ⊢ τ2 wf) → (Θ ⊢ (TTSub τ1 τ2) wf)
  wf-TTSub wf1 WFVarZ = {!   !}
  wf-TTSub wf1 (WFVarS wf2) = {!   !}
  wf-TTSub wf1 WFBase = WFBase
  wf-TTSub wf1 WFHole = WFHole
  wf-TTSub wf1 (WFArr wf2 wf3) = WFArr (wf-TTSub wf1 wf2) (wf-TTSub wf1 wf3)
  wf-TTSub wf1 (WFForall wf2) = WFForall {!   !}
  
  wf-▸arr : ∀{τ τ1 τ2 Θ} → τ ▸arr (τ1 ==> τ2) → Θ ⊢ τ wf → ((Θ ⊢ τ1 wf) × (Θ ⊢ τ2 wf))
  wf-▸arr MAHole wf = wf , wf
  wf-▸arr MAArr (WFArr wf1 wf2) = wf1 , wf2

  wf-▸forall : ∀{τ τ' Θ} → τ ▸forall (·∀ τ') → Θ ⊢ τ wf → (1+ Θ ⊢ τ' wf)
  wf-▸forall MFHole wf = weakening wf 
  wf-▸forall MFForall (WFForall wf) = wf
  
  wf-syn : ∀{τ e Θ Γ} → 
    (Θ ⊢ Γ ctxwf) → 
    (Θ , Γ ⊢ e => τ) → 
    Θ ⊢ τ wf
  wf-syn ctxwf SConst = WFBase
  wf-syn ctxwf (SAsc x x₁) = x
  wf-syn ctxwf (SVar x) = wf-ctx-var ctxwf x
  wf-syn ctxwf (SAp syn x x₁) = π2 (wf-▸arr x (wf-syn ctxwf syn)) 
  wf-syn ctxwf SEHole = WFHole
  wf-syn ctxwf (SNEHole syn) = WFHole
  wf-syn ctxwf (SLam x syn) = WFArr x (wf-syn (CtxWFExtend x ctxwf) syn)
  wf-syn ctxwf (STLam syn) = WFForall (wf-syn (weakening-ctx ctxwf) syn)   
  wf-syn ctxwf (STAp wf syn match subst) rewrite (sym subst) = wf-TTSub wf (wf-▸forall match (wf-syn ctxwf syn)) 
  
  -- recycling bin

  --   -- wf-TTsub : ∀{Θ τ1 τ2} → (Θ ⊢ τ1 wf) → (1+ Θ ⊢ τ2 wf) → (Θ ⊢ TT[ τ1 / Θ ] τ2 wf)
  -- -- wf-TTsub {Θ = Θ} wf1 WFVarZ with natEQ Θ Z
  -- -- wf-TTsub {Θ = Θ} wf1 WFVarZ | Inl refl = wf1 
  -- -- wf-TTsub {Θ = Z} wf1 WFVarZ | Inr neq = abort (neq refl)
  -- -- wf-TTsub {Θ = 1+ Θ} wf1 WFVarZ | Inr neq = WFVarZ
  -- -- wf-TTsub {Θ = Θ} wf1 (WFVarS {m = m} wf2) with natEQ Θ (1+ m) 
  -- -- wf-TTsub {Θ = Θ} wf1 (WFVarS wf2) | Inl refl = wf1
  -- -- wf-TTsub {Θ = Θ} wf1 (WFVarS wf2) | Inr neq = strengthen-var neq wf2
  -- -- wf-TTsub wf1 WFBase = WFBase
  -- -- wf-TTsub wf1 WFHole = WFHole
  -- -- wf-TTsub wf1 (WFArr wf2 wf3) = WFArr (wf-TTsub wf1 wf2) (wf-TTsub wf1 wf3)
  -- -- wf-TTsub wf1 (WFForall wf2) = WFForall (wf-TTsub (weakening wf1) wf2)

  -- -- wf-↑Nat : ∀{Θ m x} → Θ ⊢ T x wf → (1+ (1+ Θ)) ⊢ T (↑Nat 1 m (1+ x)) wf
  -- -- wf-↑Nat {m = Z} {x = Z} wf = WFVarS (WFVarS wf)
  -- -- wf-↑Nat {m = Z} {x = 1+ x} wf rewrite (↑10 x) = WFVarS (WFVarS wf)
  -- -- wf-↑Nat {m = 1+ m} wf = WFVarS {!   !}

  -- wf-↑Nat : ∀{Θ m x} → Θ ⊢ T x wf → (1+ Θ) ⊢ T (↑Nat m x) wf
  -- wf-↑Nat {m = Z} {x = Z} wf = (WFVarS wf)
  -- wf-↑Nat {m = Z} {x = 1+ x} wf rewrite (↑10 x) = (WFVarS wf)
  -- wf-↑Nat {m = 1+ m} {x = Z} wf = WFVarZ
  -- wf-↑Nat {Θ = 1+ Θ} {m = 1+ m} {x = 1+ x} (WFVarS wf) = (WFVarS (wf-↑Nat wf))

  -- wf-↑ : ∀{Θ τ n} → (Θ ⊢ τ wf) → (1+ Θ ⊢ ↑ n τ wf)
  -- wf-↑ {n = n} WFVarZ with n 
  -- ... | Z = WFVarS WFVarZ
  -- ... | 1+ n = WFVarZ
  -- wf-↑ (WFVarS wf) = wf-↑Nat (WFVarS wf)
  -- wf-↑ WFBase = WFBase
  -- wf-↑ WFHole = WFHole
  -- wf-↑ (WFArr wf wf₁) = WFArr (wf-↑ wf) (wf-↑ wf₁)
  -- wf-↑ (WFForall wf) = WFForall (wf-↑ wf)

  -- wf-TTsub2 : ∀{Θ n τ1 τ2} → (Θ ⊢ τ1 wf) → (1+ (Θ nat+ n) ⊢ τ2 wf) → (Θ ⊢ TT[ τ1 / n ] τ2 wf)
  -- -- wf-TTsub2 {Θ = Θ} wf1 WFVarZ with natEQ Θ Z
  -- -- wf-TTsub2 {Θ = Θ} wf1 WFVarZ | Inl refl = wf1 
  -- -- wf-TTsub2 {Θ = Z} wf1 WFVarZ | Inr neq = abort (neq refl)
  -- -- wf-TTsub2 wf1 WFVarZ | Inr neq = wf1
  -- -- wf-TTsub2 {Θ = Θ} wf1 (WFVarS {m = m} wf2) with natEQ Z Z --Θ (1+ m)
  -- -- wf-TTsub2 {Θ = Θ} wf1 (WFVarS wf2) | Inl refl =  {!   !}
  -- -- wf-TTsub2 {Θ = Θ} wf1 (WFVarS wf2) | Inr neq =  {!   !} --strengthen-var neq wf2
  -- wf-TTsub2 wf1 WFBase = WFBase
  -- wf-TTsub2 wf1 WFHole = WFHole
  -- wf-TTsub2 wf1 (WFArr wf2 wf3) = WFArr (wf-TTsub2 wf1 wf2) (wf-TTsub2 wf1 wf3)
  -- wf-TTsub2 wf1 (WFForall wf2) = WFForall {! wf-TTsub2 ? wf2  !} -- (wf-TTsub2 ((wf-↑ wf1)) {! wf2  !})
  -- wf-TTsub2 {Θ = Θ} wf1 wf2 = {!   !}
