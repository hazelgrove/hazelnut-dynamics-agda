{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-weakening
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-subst
open import debruijn.debruijn-lemmas-wf

module debruijn.debruijn-typing-subst where

  -- TtSub section

  inctx-sub : ∀ {n m Γ τ1 τ2} → 
    (n , τ2 ∈ Γ) → 
    n , (TTSub m τ1 τ2) ∈ (TCtxSub m τ1 Γ)
  inctx-sub InCtxZ = InCtxZ
  inctx-sub (InCtx1+ inctx) = InCtx1+ (inctx-sub inctx)

  helper-weaken : ∀{Θ n τ} → 1+ Θ ⊢ τ wf → 1+ (n nat+ Θ) ⊢ τ wf
  helper-weaken {Θ = Θ} {n = n} wf with weakening-n {Θ = 1+ Θ} {n = n} wf
  ... | result rewrite nat+1+ n Θ = result

  wt-TtSub-helper : ∀{Θ Γ d n τ1 τ2} →
    (1+ (n nat+ Θ) ⊢ Γ ctxwf) → 
    (Θ ⊢ τ1 wf) → 
    (1+ (n nat+ Θ) , Γ ⊢ d :: τ2) → 
    ((n nat+ Θ) , TCtxSub n τ1 Γ ⊢ TtSub n τ1 d :: TTSub n τ1 τ2)
  wt-TtSub-helper ctxwf wf TAConst = TAConst
  wt-TtSub-helper ctxwf wf (TAVar inctx) = TAVar (inctx-sub inctx)
  wt-TtSub-helper {n = Z} ctxwf wf1 (TALam wf2 wt) = TALam (wf-TTSub wf1 wf2) (wt-TtSub-helper (CtxWFExtend wf2 ctxwf) wf1 wt)
  wt-TtSub-helper {Θ = Θ} {n = n} ctxwf wf1 (TALam wf2 wt) with wt-TtSub-helper {n = n} (CtxWFExtend wf2 ctxwf) wf1 wt
  ... | wt2 rewrite nat+1+ n Θ = TALam (wf-TTSub-helper wf1 wf2) wt2
  wt-TtSub-helper {Θ = Θ} {n = n} {τ1 = τ1} ctxwf wf (TATLam wt) with wt-TtSub-helper {Θ = Θ} {n = 1+ n} (weakening-ctx ctxwf) wf wt
  ... | result rewrite sym (↑compose Z (1+ n) τ1) rewrite nat+1+ n Θ = TATLam {! result  !}
  wt-TtSub-helper ctxwf wf (TAAp wt1 wt2) = TAAp (wt-TtSub-helper ctxwf wf wt1) (wt-TtSub-helper ctxwf wf wt2)
  wt-TtSub-helper {Θ = Θ} {n = n} {τ1 = τ1} ctxwf wf (TATAp {τ1 = τ2} {τ2 = τ3} x wt refl) with SubSub {n = n} {τ1 = τ1} {τ2 = τ2} {τ3 = τ3} 
  ... | result rewrite sym (↑compose Z (1+ n) τ1) = TATAp (wf-TTSub-helper wf x) (wt-TtSub-helper ctxwf wf wt) (sym result)
  wt-TtSub-helper ctxwf wf (TAEHole x) = TAEHole (wf-TTSub-helper wf x)
  wt-TtSub-helper ctxwf wf (TANEHole x wt) = TANEHole (wf-TTSub-helper wf x) (wt-TtSub-helper ctxwf wf wt)
  wt-TtSub-helper {n = n} ctxwf wf (TACast wt x x₁) = TACast (wt-TtSub-helper ctxwf wf wt) (wf-TTSub-helper wf x) (~TTSub-helper (weakening-n {n = n} (wf-ta ctxwf wt)) (weakening-n x) x₁) 
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GBase GBase incon) = abort (incon ConsistBase)
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GArr GArr incon) = abort (incon (ConsistArr ConsistHole1 ConsistHole1))
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GForall GForall incon) = abort (incon (ConsistForall ConsistHole1))
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GBase GArr incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GBase GArr incon
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GBase GForall incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GBase GForall incon
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GArr GBase incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GArr GBase incon
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GArr GForall incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GArr GForall incon
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GForall GBase incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GForall GBase incon
  wt-TtSub-helper ctxwf wf (TAFailedCast wt GForall GArr incon) = TAFailedCast (wt-TtSub-helper ctxwf wf wt) GForall GArr incon

  wt-TtSub : ∀{Θ Γ d τ1 τ2} →
    (1+ Θ ⊢ Γ ctxwf) → 
    (Θ ⊢ τ1 wf) → 
    (1+ Θ , Γ ⊢ d :: τ2) → 
    (Θ , TCtxSub Z τ1 Γ ⊢ TtSub Z τ1 d :: TTSub Z τ1 τ2)
  wt-TtSub ctxwf wf wt = wt-TtSub-helper ctxwf wf wt

  -- ttSub section

  shift-helper : ∀{Γ1 Γ2 m τ1 τ2} → (m == ctx-len Γ2 → ⊥) → (m , τ2 ∈ (Γ2 ctx+ (τ1 , Γ1))) → (↓Nat (ctx-len Γ2) 1 m , τ2 ∈ (Γ2 ctx+ Γ1))
  shift-helper {Γ2 = ∅} {m = Z} neq inctx = abort (neq refl)
  shift-helper {Γ2 = ∅} {m = 1+ m} neq (InCtx1+ inctx) = inctx
  shift-helper {Γ2 = x , Γ2} neq InCtxZ = InCtxZ
  shift-helper {Γ2 = x , Γ2} neq (InCtx1+ inctx) = InCtx1+ (shift-helper (h1 neq) inctx)
    where 
      h1 : {a b : Nat} → (1+ a == 1+ b → ⊥) → (a == b) → ⊥ 
      h1 neq refl = neq refl

  ctx-access : ∀{Γ1 Γ2 τ1 τ2} → ctx-len Γ2 , τ2 ∈ (Γ2 ctx+ (τ1 , Γ1)) → τ2 == τ1
  ctx-access {Γ2 = ∅} InCtxZ = refl
  ctx-access {Γ2 = x , Γ2} (InCtx1+ inctx) = ctx-access inctx

  ctx-access-shift : ∀{Γ1 Γ2 Γ3 τ n} →  n , τ ∈ (Γ3 ctx+ Γ1) → ↑Nat (ctx-len Γ3) (ctx-len Γ2) n , τ ∈ (Γ3 ctx+ (Γ2 ctx+ Γ1))
  ctx-access-shift {Γ2 = ∅} {Γ3 = ∅} inctx = inctx
  ctx-access-shift {Γ2 = x , Γ2} {Γ3 = ∅} inctx = InCtx1+ (ctx-access-shift inctx)
  ctx-access-shift {Γ3 = x , Γ3} {n = Z} InCtxZ = InCtxZ
  ctx-access-shift {Γ3 = x , Γ3} {n = 1+ n} (InCtx1+ inctx) = InCtx1+ (ctx-access-shift inctx)

  wt-shift : ∀{Θ Γ1 Γ2 Γ3 n d τ} → (Θ , Γ3 ctx+ Γ1 ⊢ d :: τ) → ((n nat+ Θ) , (Γ3 ctx+ (Γ2 ctx+ Γ1)) ⊢ ↑d (ctx-len Γ3) (ctx-len Γ2) d :: τ)
  wt-shift TAConst = TAConst
  wt-shift (TAVar x) = TAVar (ctx-access-shift x)
  wt-shift {Γ3 = Γ3} (TALam {τ1 = τ1} x wt) = TALam (weakening-n x) (wt-shift {Γ3 = τ1 , Γ3} wt)
  wt-shift {Θ = Θ} {n = n} (TATLam wt) with wt-shift {n = n} wt 
  ... | result rewrite nat+1+ n Θ = TATLam result
  wt-shift (TAAp wt wt₁) = TAAp (wt-shift wt) (wt-shift wt₁)
  wt-shift (TATAp x wt x₁) = TATAp (weakening-n x) (wt-shift wt) x₁
  wt-shift (TAEHole x) = TAEHole (weakening-n x)
  wt-shift (TANEHole x wt) = TANEHole (weakening-n x) (wt-shift wt)
  wt-shift (TACast wt x x₁) = TACast (wt-shift wt) (weakening-n x) x₁
  wt-shift (TAFailedCast wt x x₁ x₂) = TAFailedCast (wt-shift wt) x x₁ x₂

  wt-ttSub-helper : ∀{Θ Γ1 Γ2 n d1 d2 τ1 τ2} →
    (Θ ⊢ τ1 wf) → 
    (Θ , Γ1 ⊢ d1 :: τ1) → 
    (n nat+ Θ) , Γ2 ctx+ (τ1 , Γ1) ⊢ d2 :: τ2 → 
    (n nat+ Θ) , Γ2 ctx+ Γ1 ⊢ ↓d (ctx-len Γ2) 1 ([ ↑d Z (ctx-len Γ2 nat+ 1) d1 / (ctx-len Γ2) ] d2) :: τ2
  wt-ttSub-helper wf wt1 TAConst = TAConst
  wt-ttSub-helper {Γ2 = Γ2} {n = n} {d1 = d1} wf wt1 (TAVar {n = m} inctx) with natEQ m (ctx-len Γ2) 
  wt-ttSub-helper {Γ2 = Γ2} {n = n} {d1 = d1} wf wt1 (TAVar {n = m} inctx) | Inl refl rewrite ctx-access inctx with ↓↑d-invert {n = ctx-len Γ2} {m = Z} {d = d1} 
  wt-ttSub-helper {Γ2 = Γ2} {n = n} {d1 = d1} wf wt1 (TAVar {n = m} inctx) | Inl refl | result rewrite nat+Z (ctx-len Γ2) rewrite result = wt-shift wt1 
  wt-ttSub-helper {Γ2 = Γ2} {n = n} {d1 = d1} wf wt1 (TAVar {n = m} inctx) | Inr neq = TAVar (shift-helper neq inctx)
  wt-ttSub-helper {Γ2 = Γ2} {d1 = d1} wf wt1 (TALam {τ1 = τ1} x wt2) with wt-ttSub-helper {Γ2 = (τ1 , Γ2)} wf wt1 wt2 
  ... | result rewrite ↑d-compose Z (ctx-len Γ2 nat+ 1) d1 = TALam x result
  wt-ttSub-helper wf wt1 (TATLam wt2) = TATLam (wt-ttSub-helper wf wt1 wt2)
  wt-ttSub-helper wf wt1 (TAAp wt2 wt3) = TAAp (wt-ttSub-helper wf wt1 wt2) (wt-ttSub-helper wf wt1 wt3)
  wt-ttSub-helper wf wt1 (TATAp x wt2 x₁) = TATAp x (wt-ttSub-helper wf wt1 wt2) x₁
  wt-ttSub-helper wf wt1 (TAEHole x) = TAEHole x
  wt-ttSub-helper wf wt1 (TANEHole x wt2) = TANEHole x (wt-ttSub-helper wf wt1 wt2)
  wt-ttSub-helper wf wt1 (TACast wt2 x x₁) = TACast (wt-ttSub-helper wf wt1 wt2) x x₁
  wt-ttSub-helper wf wt1 (TAFailedCast wt2 x x₁ x₂) = TAFailedCast (wt-ttSub-helper wf wt1 wt2) x x₁ x₂

  wt-ttSub : ∀{Θ d1 d2 τ1 τ2} →
    (Θ ⊢ τ1 wf) → 
    (Θ , ∅ ⊢ d1 :: τ1) → 
    (Θ , (τ1 , ∅) ⊢ d2 :: τ2) → 
    (Θ , ∅ ⊢ ttSub d1 d2 :: τ2)
  wt-ttSub wf wt1 wt2 = wt-ttSub-helper wf wt1 wt2
 