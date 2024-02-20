-- {-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
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
  wt-TtSub-helper {Θ = Θ} {n = n} {τ1 = τ1} ctxwf wf (TATLam wt) with wt-TtSub-helper {Θ = Θ} {n = 1+ n} {!   !} wf wt
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

  -- required theorem : Z ⊢ τ1 wf -> 1 , ∅ ⊢ d :: τ2 -> Z , ∅ ⊢ TtSub Z τ1 d :: TTSub Z τ1 τ2

  -- ttSub section

  shift-helper : ∀{Γ1 Γ2 Θ2 m τ1 τ2} → (m == ctx-len Γ2 → ⊥) → (m , τ2 ∈ ↑ctx Z Θ2 (Γ2 ctx+ (τ1 , Γ1))) → (↓Nat (ctx-len Γ2) 1 m , τ2 ∈ ↑ctx 0 Θ2 (Γ2 ctx+ Γ1))
  shift-helper {Γ2 = ∅} {m = Z} neq inctx = abort (neq refl)
  shift-helper {Γ2 = ∅} {m = 1+ m} neq (InCtx1+ inctx) = inctx
  shift-helper {Γ2 = x , Γ2} neq InCtxZ = InCtxZ
  shift-helper {Γ2 = x , Γ2} neq (InCtx1+ inctx) = InCtx1+ (shift-helper (h1 neq) inctx)
    where 
      h1 : {a b : Nat} → (1+ a == 1+ b → ⊥) → (a == b) → ⊥ 
      h1 neq refl = neq refl

  ctx-access : ∀{Γ1 Γ2 τ1 τ2 n} → ctx-len Γ2 , τ2 ∈ ↑ctx 0 n (Γ2 ctx+ (τ1 , Γ1)) → τ2 == ↑ 0 n τ1
  ctx-access {Γ2 = ∅} InCtxZ = refl
  ctx-access {Γ2 = x , Γ2} (InCtx1+ inctx) = ctx-access inctx

  ctx-access-shift : ∀{Γ1 Γ2 Γ3 τ n m} →  n , τ ∈ (Γ3 ctx+ Γ1) → ↑Nat (ctx-len Γ3) (ctx-len Γ2) n , ↑ Z m τ ∈ ↑ctx Z m (Γ3 ctx+ (Γ2 ctx+ Γ1))
  ctx-access-shift {Γ2 = ∅} {Γ3 = ∅} InCtxZ = InCtxZ
  ctx-access-shift {Γ2 = ∅} {Γ3 = ∅} (InCtx1+ inctx) = InCtx1+ (ctx-access-shift inctx)
  ctx-access-shift {Γ2 = x , Γ2} {Γ3 = ∅} inctx = InCtx1+ (ctx-access-shift inctx)
  ctx-access-shift {Γ3 = x , Γ3} {n = Z} InCtxZ = InCtxZ
  ctx-access-shift {Γ3 = x , Γ3} {n = 1+ n} (InCtx1+ inctx) = InCtx1+ (ctx-access-shift inctx)

  -- wt-shift : ∀{Θ Γ1 Γ2 Γ3 n d τ} → (Θ , Γ3 ctx+ Γ1 ⊢ d :: τ) → ((n nat+ Θ) , ↑ctx Z n (Γ3 ctx+ (Γ2 ctx+ Γ1)) ⊢ ↑d (ctx-len Γ3) (ctx-len Γ2) d :: ↑ Z n τ)
  -- wt-shift TAConst = TAConst
  -- wt-shift (TAVar x) = TAVar (ctx-access-shift x)
  -- wt-shift {Γ3 = Γ3} (TALam {τ1 = τ1} x wt) = {!  TALam ? ? !} --TALam (weakening-n x) (wt-shift {Γ3 = τ1 , Γ3} wt)
  -- wt-shift {Θ = Θ} {n = n} (TATLam wt) = {!   !}
  -- -- with wt-shift {n = n} wt 
  -- -- ... | result rewrite nat+1+ n Θ = TATLam result
  -- wt-shift (TAAp wt wt₁) = TAAp (wt-shift wt) (wt-shift wt₁)
  -- wt-shift (TATAp x wt x₁) = {!   !} --TATAp (weakening-n x) (wt-shift wt) x₁
  -- wt-shift (TAEHole x) = {!   !} --TAEHole (weakening-n x)
  -- wt-shift (TANEHole x wt) = {!   !} --TANEHole (weakening-n x) (wt-shift wt)
  -- wt-shift (TACast wt x x₁) = {!   !} --TACast (wt-shift wt) (weakening-n x) x₁
  -- wt-shift (TAFailedCast wt x x₁ x₂) = {!   !} --TAFailedCast (wt-shift wt) x x₁ x₂

  inctx-shift : ∀{n τ Γ} → n , τ ∈ ↑ctx Z 1 Γ → Σ[ τ' ∈ htyp ] (n , τ' ∈ Γ × ↑ Z 1 τ' == τ)
  inctx-shift {Γ = x , Γ} InCtxZ = x , InCtxZ , refl
  inctx-shift {Γ = x , Γ} (InCtx1+ inctx) with inctx-shift inctx 
  ... | τ' , inctx' , eq = τ' , InCtx1+ inctx' , eq
  
  other-inctx-shift : ∀{n τ Γ} → n , τ ∈ Γ → n , ↑ 0 1 τ ∈ ↑ctx 0 1 Γ
  other-inctx-shift InCtxZ = InCtxZ
  other-inctx-shift (InCtx1+ inctx) = InCtx1+ (other-inctx-shift inctx)

  data consist : (Θ1 Θ2 n m : Nat) → (Γ1 Γ2 Γ3 : ctx) → (τ : htyp) → Set where 
    ConBase : ∀{Θ τ} → consist Θ Θ Z Z ∅ (τ , ∅) ∅ τ
    ConLam : ∀{Θ1 Θ2 n m Γ1 Γ2 Γ3 τ1 τ2} → consist Θ1 Θ2 n m Γ1 Γ2 Γ3 τ1 → Θ2 ⊢ τ2 wf → consist Θ1 Θ2 (1+ n) m Γ1 (τ2 , Γ2) (τ2 , Γ3) τ1
    ConTLam : ∀{Θ1 Θ2 n m Γ1 Γ2 Γ3 τ} → consist Θ1 Θ2 n m Γ1 Γ2 Γ3 τ → consist Θ1 (1+ Θ2) n (1+ m) Γ1 (↑ctx Z 1 Γ2) (↑ctx Z 1 Γ3) τ

  var-hit : ∀{Θ1 Θ2 n m d Γ1 Γ2 Γ3 τ1 τ2} →
    consist Θ1 Θ2 n m Γ1 Γ2 Γ3 τ1 →
    n , τ2 ∈ Γ2 →
    Θ1 , Γ1 ⊢ d :: τ1 →
    Θ2 , Γ3 ⊢ ↑d 0 n (↑td 0 m d) :: τ2
  var-hit {n = n} {m = m} {d = d} ConBase InCtxZ wt rewrite ↑tdZ m d rewrite ↑dZ n d = wt
  var-hit (ConLam con x) (InCtx1+ inctx) wt = wt-inc-t (var-hit con inctx wt)
    where
      wt-inc-t : ∀{Θ n d Γ τ τ'} → Θ , Γ ⊢ ↑d Z n d :: τ → Θ , (τ' , Γ) ⊢ ↑d Z (1+ n) d :: τ
      wt-inc-t {d = c} TAConst = TAConst
      wt-inc-t {d = X x} (TAVar x₁) = TAVar (InCtx1+ x₁) 
      wt-inc-t {d = ·λ[ x ] d} (TALam x₁ wt) = {!   !}
      wt-inc-t {d = ·Λ d} (TATLam wt) = TATLam (wt-inc-t wt)
      wt-inc-t {d = ⦇-⦈⟨ x ⟩} (TAEHole x₁) = TAEHole x₁
      wt-inc-t {d = ⦇⌜ d ⌟⦈⟨ x ⟩} (TANEHole x₁ wt) = TANEHole x₁ (wt-inc-t wt)
      wt-inc-t {d = d ∘ d₁} (TAAp wt wt₁) = TAAp (wt-inc-t wt) (wt-inc-t wt₁)
      wt-inc-t {d = d < x >} (TATAp x₁ wt x₂) = TATAp x₁ (wt-inc-t wt) x₂
      wt-inc-t {d = d ⟨ x ⇒ x₁ ⟩} (TACast wt x₂ x₃) = TACast (wt-inc-t wt) x₂ x₃
      wt-inc-t {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} (TAFailedCast wt x₂ x₃ x₄) = TAFailedCast (wt-inc-t wt) x₂ x₃ x₄
  var-hit (ConTLam con) inctx wt with inctx-shift inctx 
  var-hit (ConTLam con) inctx wt | τ' , inctx' , refl = wt-inc-T (var-hit con inctx' wt)
    where
      wt-inc-T : ∀{Θ n m d Γ τ} → Θ , Γ ⊢ ↑d 0 n (↑td 0 m d) :: τ → 1+ Θ , ↑ctx Z 1 Γ ⊢ ↑d 0 n (↑td Z (1+ m) d) :: ↑ 0 1 τ
      wt-inc-T = {!   !}

  var-miss : ∀{Θ1 Θ2 n m' Γ1 Γ2 Γ3 m τ τ'} →
    consist Θ1 Θ2 n m' Γ1 Γ2 Γ3 τ' →
    m , τ ∈ Γ2 →
    m ≠ n →
    ↓Nat n 1 m , τ ∈ Γ3
  var-miss ConBase InCtxZ neq = abort (neq refl)
  var-miss (ConLam con x) InCtxZ neq = InCtxZ
  var-miss (ConLam con x) (InCtx1+ inctx) neq = InCtx1+ (var-miss con inctx λ x₂ → neq (inj x₂))
    where 
      inj : ∀{n m} → n == m → 1+ n == 1+ m
      inj refl = refl
  var-miss (ConTLam {Γ3 = Γ3} con) inctx neq with inctx-shift inctx 
  var-miss (ConTLam {Γ3 = Γ3} con) inctx neq | τ' , inctx' , refl = other-inctx-shift (var-miss con inctx' neq)

  wt-ttSub-helper : ∀{Θ1 Θ2 Γ1 Γ2 Γ3 n m τ1 τ2 d1 d2} →
    consist Θ1 Θ2 n m Γ1 Γ2 Γ3 τ1 →
    Θ1 , Γ1 ⊢ d1 :: τ1 → 
    Θ2 , Γ2 ⊢ d2 :: τ2 →
    Θ2 , Γ3 ⊢ ttSub n m d1 d2 :: τ2
  wt-ttSub-helper con wt1 TAConst = TAConst
  wt-ttSub-helper con wt1 (TAAp wt2 wt3) = TAAp (wt-ttSub-helper con wt1 wt2) (wt-ttSub-helper con wt1 wt3)
  wt-ttSub-helper con wt1 (TATAp x wt2 x₁) = TATAp x (wt-ttSub-helper con wt1 wt2) x₁
  wt-ttSub-helper con wt1 (TAEHole x) = TAEHole x
  wt-ttSub-helper con wt1 (TANEHole x wt2) = TANEHole x (wt-ttSub-helper con wt1 wt2)
  wt-ttSub-helper con wt1 (TACast wt2 x x₁) = TACast (wt-ttSub-helper con wt1 wt2) x x₁
  wt-ttSub-helper con wt1 (TAFailedCast wt2 x x₁ x₂) = TAFailedCast (wt-ttSub-helper con wt1 wt2) x x₁ x₂
  wt-ttSub-helper {n = n} {m = m} {d1 = d1} con wt1 (TALam x wt2) with wt-ttSub-helper (ConLam con x) wt1 wt2 
  ... | result rewrite ↑d-↑td-comm {1} {m} {Z} {Z} {d = (↑d 0 (1+ n) d1)} rewrite ↑d-compose Z (1+ n) d1 = TALam x result
  wt-ttSub-helper {n = n} {m = m} {d1 = d1} con wt1 (TATLam wt2) with wt-ttSub-helper (ConTLam con) wt1 wt2
  ... | result rewrite ↑td-compose 0 m (↑d 0 (1+ n) d1) = TATLam result 
  wt-ttSub-helper {n = n} {d1 = d1} con wt1 (TAVar {n = x} inctx) with natEQ x n 
  wt-ttSub-helper {n = n} {d1 = d1} con wt1 (TAVar {n = x} inctx) | Inl refl with ↓↑d-invert {n} {Z} {d1}
  wt-ttSub-helper {n = n} {m = m} {d1 = d1} con wt1 (TAVar {n = x} inctx) | Inl refl | result 
    rewrite sym (↑d-↑td-comm {1+ n} {m} {Z} {Z} {d1}) with ↓↑d-invert {n} {Z} {(↑td 0 m d1)} 
  ... | eq rewrite nat+1+ n Z rewrite nat+Z n rewrite eq = var-hit con inctx wt1    
  wt-ttSub-helper {n = n} {d1 = d1} con wt1 (TAVar {n = m} inctx) | Inr neq = TAVar (var-miss con inctx neq)
  
  wt-ttSub : ∀{Θ d1 d2 τ1 τ2} →
    (Θ , ∅ ⊢ d1 :: τ1) → 
    (Θ , (τ1 , ∅) ⊢ d2 :: τ2) → 
    (Θ , ∅ ⊢ ttSub Z Z d1 d2 :: τ2)
  wt-ttSub {Θ = Θ} {d2 = d2} {τ1 = τ1} {τ2 = τ2}  wt1 wt2 = wt-ttSub-helper ConBase wt1 wt2
    where 
      wt2' : Θ , (↑ Z Z τ1 , ∅) ⊢ d2 :: τ2
      wt2' rewrite ↑Z Z τ1 = wt2
  