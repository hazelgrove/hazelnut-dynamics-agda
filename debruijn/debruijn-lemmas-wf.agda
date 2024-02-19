open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-weakening
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-subst

module debruijn.debruijn-lemmas-wf where

  wf-ctx-var : ∀{τ n Θ Γ} → 
    (Θ ⊢ Γ ctxwf) →
    (n , τ ∈ Γ) → 
    Θ ⊢ τ wf
  wf-ctx-var (CtxWFExtend x ctxwf) InCtxZ = x
  wf-ctx-var (CtxWFExtend x ctxwf) (InCtx1+ inctx) = wf-ctx-var ctxwf inctx

  wf-inc : ∀{Θ τ m} → Θ ⊢ τ wf → 1+ Θ ⊢ ↑ m 1 τ wf
  wf-inc {m = Z} WFVarZ = WFVarS WFVarZ
  wf-inc {m = 1+ m} WFVarZ = WFVarZ
  wf-inc {m = Z} (WFVarS wf) = WFVarS (WFVarS wf)
  wf-inc {m = 1+ m} (WFVarS wf) = WFVarS (wf-inc wf)
  wf-inc WFBase = WFBase
  wf-inc WFHole = WFHole
  wf-inc (WFArr wf wf₁) = WFArr (wf-inc wf) (wf-inc wf₁)
  wf-inc (WFForall wf) = WFForall (wf-inc wf)

  wf-ctx-inc : ∀{Θ Γ} → Θ ⊢ Γ ctxwf → 1+ Θ ⊢ ↑ctx Z 1 Γ ctxwf
  wf-ctx-inc CtxWFEmpty = CtxWFEmpty
  wf-ctx-inc (CtxWFExtend x ctxwf) = CtxWFExtend (wf-inc x) (wf-ctx-inc ctxwf)

  wf-⊑t : ∀{Θ τ1 τ2} → Θ ⊢ τ1 wf → τ1 ⊑t τ2 → Θ ⊢ τ2 wf
  wf-⊑t wf PTBase = wf 
  wf-⊑t _ PTHole = WFHole
  wf-⊑t wf PTTVar = wf
  wf-⊑t (WFArr wf1 wf2) (PTArr prec1 prec2) = WFArr (wf-⊑t wf1 prec1) (wf-⊑t wf2 prec2)
  wf-⊑t (WFForall wf) (PTForall prec) = WFForall (wf-⊑t wf prec)

  wf-⊓ : ∀{τ1 τ2 τ3 Θ} → τ1 ⊓ τ2 == τ3 → Θ ⊢ τ1 wf → Θ ⊢ τ2 wf → Θ ⊢ τ3 wf
  wf-⊓ MeetHoleL wf1 wf2 = wf2 
  wf-⊓ MeetHoleR wf1 wf2 = wf1
  wf-⊓ MeetBase wf1 wf2 = wf2
  wf-⊓ MeetVar wf1 wf2 = wf2
  wf-⊓ (MeetArr meet meet₁) (WFArr wf1 wf2) (WFArr wf3 wf4) = WFArr (wf-⊓ meet wf1 wf3) (wf-⊓ meet₁ wf2 wf4)
  wf-⊓ (MeetForall meet) (WFForall wf1) (WFForall wf2) = WFForall (wf-⊓ meet wf1 wf2)
  
  -- wf-▸arr : ∀{τ τ1 τ2 Θ} → τ ▸arr (τ1 ==> τ2) → Θ ⊢ τ wf → ((Θ ⊢ τ1 wf) × (Θ ⊢ τ2 wf))
  -- wf-▸arr MAHole wf = wf , wf
  -- wf-▸arr MAArr (WFArr wf1 wf2) = wf1 , wf2

  -- wf-▸forall : ∀{τ τ' Θ} → τ ▸forall (·∀ τ') → Θ ⊢ τ wf → (1+ Θ ⊢ τ' wf)
  -- wf-▸forall MFHole wf = weakening wf 
  -- wf-▸forall MFForall (WFForall wf) = wf
  
  wf-syn : ∀{τ e Θ Γ} → 
    (Θ ⊢ Γ ctxwf) → 
    (Θ , Γ ⊢ e => τ) → 
    Θ ⊢ τ wf
  wf-syn ctxwf SConst = WFBase
  wf-syn ctxwf (SAsc x x₁) = x
  wf-syn ctxwf (SVar x) = wf-ctx-var ctxwf x
  wf-syn ctxwf (SAp syn meet _) with wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
  ... | WFArr _ wf = wf
  wf-syn ctxwf SEHole = WFHole
  wf-syn ctxwf (SNEHole syn) = WFHole
  wf-syn ctxwf (SLam x syn) = WFArr x (wf-syn (CtxWFExtend x ctxwf) syn)
  wf-syn ctxwf (STLam syn) = WFForall (wf-syn (wf-ctx-inc ctxwf) syn)
  wf-syn ctxwf (STAp wf syn meet refl) with wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole) 
  ... | WFForall wf' = wf-TTSub wf wf'
  
  wf-elab-syn : ∀{τ e d Θ Γ} → 
    (Θ ⊢ Γ ctxwf) → 
    (Θ , Γ ⊢ e ⇒ τ ~> d) → 
    Θ ⊢ τ wf
  wf-elab-syn ctxwf ESConst = WFBase
  wf-elab-syn ctxwf (ESVar x) = wf-ctx-var ctxwf x
  wf-elab-syn ctxwf (ESLam x syn) = WFArr x (wf-elab-syn (CtxWFExtend x ctxwf) syn)
  wf-elab-syn ctxwf (ESTLam syn) = WFForall (wf-elab-syn (wf-ctx-inc ctxwf) syn)
  wf-elab-syn ctxwf (ESAp syn meet _ _) with wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
  ... | WFArr _ wf = wf
  wf-elab-syn ctxwf (ESTAp wf syn meet _ refl) with wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole) 
  ... | WFForall wf' = wf-TTSub wf wf'
  wf-elab-syn ctxwf ESEHole = WFHole
  wf-elab-syn ctxwf (ESNEHole syn) = WFHole
  wf-elab-syn ctxwf (ESAsc x x₁) = x

  wf-ta : ∀{τ d Θ Γ} → 
    (Θ ⊢ Γ ctxwf) → 
    (Θ , Γ ⊢ d :: τ) → 
    Θ ⊢ τ wf
  wf-ta ctxwf TAConst = WFBase
  wf-ta ctxwf (TAVar x) = wf-ctx-var ctxwf x
  wf-ta ctxwf (TALam x wt) = WFArr x (wf-ta (CtxWFExtend x ctxwf) wt)
  wf-ta ctxwf (TATLam wt) = WFForall (wf-ta (wf-ctx-inc ctxwf) wt)
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
   -- wf-index-inc : 
  --   ∀{t i Θ τ τ'} → 
  --   ↑ t i τ == τ' → 
  --   Θ ⊢ τ' wf →
  --   (1+ Θ) ⊢ ↑ t (1+ i) τ wf
  -- wf-index-inc {t = t} {i = i} {τ = b} eq WFBase = WFBase
  -- wf-index-inc {t = t} {i = i} {τ = ⦇-⦈} eq WFHole = WFHole
  -- wf-index-inc {t = t} {i = i} {τ = τ ==> τ₁} refl (WFArr wf wf₁) = WFArr (wf-index-inc refl wf) (wf-index-inc refl wf₁)
  -- wf-index-inc {t = Z} {i = Z} {τ = T .Z} refl WFVarZ = WFVarS WFVarZ
  -- wf-index-inc {t = 1+ t} {i = i} {τ = T Z} eq WFVarZ = WFVarZ
  -- wf-index-inc {t = Z} {i = Z} {τ = T (1+ x)} refl (WFVarS wf) = WFVarS (WFVarS wf)
  -- wf-index-inc {t = Z} {i = 1+ i} {τ = T x} refl (WFVarS wf) = WFVarS (WFVarS wf)
  -- wf-index-inc {t = 1+ t} {i = i} {τ = T (1+ x)} refl (WFVarS wf) = WFVarS (wf-index-inc {t = t} {i = i} {τ = T x} refl wf)
  -- wf-index-inc {t = t} {i = i} {τ = ·∀ τ} refl (WFForall wf) = WFForall (wf-index-inc refl wf)

  -- -- wf-index-inc' : 
  -- --   ∀{t Θ τ} → 
  -- --   Θ ⊢ τ wf →
  -- --   (1+ Θ) ⊢ ↑ t 1 τ wf
  -- -- wf-index-inc' = {!   !}

  -- wf-index-up : 
  --   ∀{t i Θ τ} → 
  --   Θ ⊢ τ wf →
  --   (i nat+ Θ) ⊢ (↑ t i τ) wf
  -- wf-index-up {t = t} {i = Z} {τ = τ} wf rewrite ↑Z t τ = wf
  -- wf-index-up {t = t} {i = 1+ i} {τ = b} WFBase = WFBase
  -- wf-index-up {t = t} {i = 1+ i} {τ = ⦇-⦈} WFHole = WFHole
  -- wf-index-up {t = t} {i = 1+ i} {τ = τ ==> τ₁} (WFArr wf wf₁) = WFArr (wf-index-up wf) (wf-index-up wf₁)
  -- wf-index-up {t = Z} {i = 1+ i} {τ = T Z} WFVarZ = WFVarS (wf-index-up WFVarZ)
  -- wf-index-up {t = 1+ t} {i = 1+ i} {τ = T Z} WFVarZ = WFVarZ
  -- wf-index-up {t = Z} {i = 1+ i} {τ = T (1+ x)} (WFVarS wf) = WFVarS (wf-index-up (WFVarS wf))
  -- wf-index-up {t = 1+ t} {i = 1+ i} {τ = T (1+ x)} (WFVarS {Θ = Θ} wf) rewrite nat+1+ i Θ 
  --   = WFVarS (wf-index-inc {t = t} {i = i} refl (wf-index-up {t = t} {i = i} wf))
  -- wf-index-up {t = t} {i = 1+ i} {Θ = Θ} {τ = ·∀ τ} (WFForall wf) with wf-index-up {t = 1+ t} {i = i} wf 
  -- ... | result rewrite nat+1+ i Θ = WFForall (wf-index-inc refl result)

  -- wf-index-down : 
  --   ∀{t Θ τ} → 
  --   1+ (1+ (t nat+ Θ)) ⊢ τ wf →
  --   1+ (t nat+ Θ) ⊢ (↓ t 1 τ) wf
  -- wf-index-down = {!   !}

  -- wf-TTSub-helper1 :
  --   ∀{t n Θ τ} → 
  --   1+ (t nat+ Θ) ⊢ τ wf →
  --   1+ ((n nat+ t) nat+ Θ) ⊢ ↓ (n nat+ t) 1 (↑ t (1+ n) τ) wf
  -- wf-TTSub-helper1 {t = t} {n = n} {Θ = Θ} wf with wf-index-up {t = t} {i = 1+ n} wf
  -- ... | result rewrite nat+1+ n (t nat+ Θ) rewrite nat+assoc n t Θ = wf-index-down result

  -- wf-TTSub-helper1 {t = Z} {i = Z} WFVarZ = WFVarZ
  -- wf-TTSub-helper1 {t = Z} {i = 1+ i} WFVarZ = WFVarS {!   !}
  -- wf-TTSub-helper1 {t = 1+ t} {i = i} WFVarZ = {!   !}
  -- wf-TTSub-helper1 {t = Z} {i = i} (WFVarS wf) = {!   !}
  -- wf-TTSub-helper1 {t = 1+ t} {i = i} (WFVarS wf) = {!   !}
  -- wf-TTSub-helper1 WFBase = WFBase
  -- wf-TTSub-helper1 WFHole = WFHole
  -- wf-TTSub-helper1 (WFArr wf wf₁) = WFArr (wf-TTSub-helper1 wf) (wf-TTSub-helper1 wf₁) 
  -- wf-TTSub-helper1 (WFForall wf) = WFForall (wf-TTSub-helper1 wf) 

  -- wf-TTSub-helper1 {n = n} {m = Z} WFVarZ = {!   !}
  -- wf-TTSub-helper1 {n = n} {m = Z} (WFVarS wf) = {!   !} 
  -- wf-TTSub-helper1 {n = n} {m = 1+ m} wf = {!   !}
  -- wf-TTSub-helper1 WFBase = WFBase
  -- wf-TTSub-helper1 WFHole = WFHole 
  -- wf-TTSub-helper1 (WFArr wf wf₁) = WFArr (wf-TTSub-helper1 wf) (wf-TTSub-helper1 wf₁)  
  -- wf-TTSub-helper1 {n = n} {m = m} (WFForall wf) = WFForall (wf-TTSub-helper1 {n = n} {m = 1+ m}  wf) 