open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-type-assignment-unicity

module debruijn.debruijn-preservation where

  wt-filling : ∀{ ε Γ d τ d' } →
    Z , Γ ⊢ d :: τ →
    d == ε ⟦ d' ⟧ →
    Σ[ τ' ∈ htyp ] (Z , Γ ⊢ d' :: τ')
  wt-filling wt FHOuter = _ , wt
  wt-filling (TAAp wt _) (FHAp1 fill) = wt-filling wt fill 
  wt-filling (TAAp _ wt) (FHAp2 fill) = wt-filling wt fill
  wt-filling (TATAp _ wt _) (FHTAp fill) = wt-filling wt fill
  wt-filling (TANEHole x wt) (FHNEHole fill) = wt-filling wt fill
  wt-filling (TACast wt x x₁) (FHCast fill) = wt-filling wt fill
  wt-filling (TAFailedCast wt x x₁ x₂) (FHFailedCast fill) = wt-filling wt fill

  wt-different-fill : ∀{ Γ d ε d1 d2 d' τ1 τ2} →
    d == ε ⟦ d1 ⟧ →
    d' == ε ⟦ d2 ⟧ →
    Z , Γ ⊢ d :: τ1 →
    Z , Γ ⊢ d1 :: τ2 →
    Z , Γ ⊢ d2 :: τ2 →
    Z , Γ ⊢ d' :: τ1
  wt-different-fill FHOuter FHOuter wt wt2 wt3 rewrite type-assignment-unicity wt wt2 = wt3
  wt-different-fill (FHAp1 fill1) (FHAp1 fill2) (TAAp wt wt1) wt2 wt3 = TAAp (wt-different-fill fill1 fill2 wt wt2 wt3) wt1
  wt-different-fill (FHAp2 fill1) (FHAp2 fill2) (TAAp wt wt1) wt2 wt3 = TAAp wt (wt-different-fill fill1 fill2 wt1 wt2 wt3)
  wt-different-fill (FHTAp fill1) (FHTAp fill2) (TATAp x wt sub) wt2 wt3 = TATAp x (wt-different-fill fill1 fill2 wt wt2 wt3) sub
  wt-different-fill (FHNEHole fill1) (FHNEHole fill2) (TANEHole x wt) wt2 wt3 = TANEHole x (wt-different-fill fill1 fill2 wt wt2 wt3)
  wt-different-fill (FHCast fill1) (FHCast fill2) (TACast wt x x₁) wt2 wt3 = TACast (wt-different-fill fill1 fill2 wt wt2 wt3) x x₁
  wt-different-fill (FHFailedCast fill1) (FHFailedCast fill2) (TAFailedCast wt x x₁ x₂) wt2 wt3 = TAFailedCast (wt-different-fill fill1 fill2 wt wt2 wt3) x x₁ x₂

  -- note: wf1 assumption might end up unecessary

  ~TTSub-helper : ∀{n τ1 τ2 τ3} → (n ⊢ τ1 wf) → (1+ n ⊢ τ2 wf) → (1+ n ⊢ τ3 wf) → τ2 ~ τ3 → (↓ n 1 (TT[ (↑ Z (1+ n) τ1) / n ] τ2)) ~ (↓ n 1 (TT[ (↑ Z (1+ n) τ1) / n ] τ3))
  ~TTSub-helper wf1 wf2 wf3 ConsistBase = ConsistBase
  ~TTSub-helper wf1 wf2 wf3 ConsistVar = ~refl
  ~TTSub-helper wf1 wf2 wf3 ConsistHole1 = ConsistHole1
  ~TTSub-helper wf1 wf2 wf3 ConsistHole2 = ConsistHole2 
  ~TTSub-helper wf1 (WFArr wf2 wf3) (WFArr wf4 wf5) (ConsistArr con1 con2) = ConsistArr (~TTSub-helper wf1 wf2 wf4 con1) (~TTSub-helper wf1 wf3 wf5 con2)
  ~TTSub-helper {n = n} {τ1 = τ1} wf1 (WFForall wf2) (WFForall wf3) (ConsistForall con) with ↑compose Z (1+ n) τ1
  ...| eq rewrite eq = ConsistForall (~TTSub-helper (weakening wf1) wf2 wf3 con)

  ~TTSub : {τ1 τ2 τ3 : htyp} → Z ⊢ τ1 wf → 1 ⊢ τ2 wf → 1 ⊢ τ3 wf → τ2 ~ τ3 → TTSub τ1 τ2 ~ TTSub τ1 τ3
  ~TTSub wf1 wf2 wf3 con = ~TTSub-helper {n = Z} wf1 wf2 wf3 con

  -- ~TTSub2 : ∀ {Θ τ1 τ2 τ3} → Θ ⊢ τ1 wf → 1+ Θ ⊢ τ2 wf → 1+ Θ ⊢ τ3 wf → τ2 ~ τ3 → TTSub τ1 τ2 ~ TTSub τ1 τ3
  -- ~TTSub2 {Θ = Θ} wf1 wf2 wf3 con = ~TTSub-helper {n = Θ} wf1 wf2 wf3 con

  inctx-sub : ∀ {n Γ τ1 τ2} → 
    (n , τ2 ∈ Γ) → 
    (n , TTSub τ1 τ2 ∈ TCtxSub τ1 Γ)
  inctx-sub InCtxZ = InCtxZ
  inctx-sub (InCtx1+ inctx) = InCtx1+ (inctx-sub inctx)

  wt-TtSub : ∀{Θ Γ d τ1 τ2} →
    (Θ ⊢ τ1 wf) → 
    (1+ Θ , Γ ⊢ d :: τ2) → 
    (Θ , TCtxSub τ1 Γ ⊢ TtSub τ1 d :: TTSub τ1 τ2)
  wt-TtSub wf TAConst = TAConst
  wt-TtSub wf (TAVar inctx) = TAVar (inctx-sub inctx)
  wt-TtSub wf1 (TALam wf2 wt) = TALam (wf-TTSub wf1 wf2) (wt-TtSub wf1 wt)
  wt-TtSub wf (TATLam wt) = TATLam {!    !}
  wt-TtSub wf (TAAp wt1 wt2) = TAAp (wt-TtSub wf wt1) (wt-TtSub wf wt2)
  wt-TtSub wf1 (TATAp wf2 wt refl) = TATAp (wf-TTSub wf1 wf2) (wt-TtSub wf1 wt) {!   !}
  wt-TtSub wf1 (TAEHole wf2) = TAEHole (wf-TTSub wf1 wf2)
  wt-TtSub wf1 (TANEHole wf2 wt) = TANEHole (wf-TTSub wf1 wf2) (wt-TtSub wf1 wt)
  wt-TtSub wf1 (TACast wt wf2 con) = TACast (wt-TtSub wf1 wt) (wf-TTSub wf1 wf2) {!   !}
  wt-TtSub wf (TAFailedCast wt GBase GBase incon) = abort (incon ConsistBase)
  wt-TtSub wf (TAFailedCast wt GArr GArr incon) = abort (incon (ConsistArr ConsistHole1 ConsistHole1))
  wt-TtSub wf (TAFailedCast wt GForall GForall incon) = abort (incon (ConsistForall ConsistHole1))
  wt-TtSub wf (TAFailedCast wt GBase GArr incon) = TAFailedCast (wt-TtSub wf wt) GBase GArr incon
  wt-TtSub wf (TAFailedCast wt GBase GForall incon) = TAFailedCast (wt-TtSub wf wt) GBase GForall incon
  wt-TtSub wf (TAFailedCast wt GArr GBase incon) = TAFailedCast (wt-TtSub wf wt) GArr GBase incon
  wt-TtSub wf (TAFailedCast wt GArr GForall incon) = TAFailedCast (wt-TtSub wf wt) GArr GForall incon
  wt-TtSub wf (TAFailedCast wt GForall GBase incon) = TAFailedCast (wt-TtSub wf wt) GForall GBase incon
  wt-TtSub wf (TAFailedCast wt GForall GArr incon) = TAFailedCast (wt-TtSub wf wt) GForall GArr incon

  shift-helper : ∀{Γ1 Γ2 m τ1 τ2} → (m == ctx-len Γ2 → ⊥) → (m , τ2 ∈ (Γ2 ctx+ (τ1 , Γ1))) → (↓Nat (ctx-len Γ2) 1 m , τ2 ∈ (Γ2 ctx+ Γ1))
  shift-helper {Γ2 = ∅} {m = Z} neq inctx = abort (neq refl)
  shift-helper {Γ2 = ∅} {m = 1+ m} neq (InCtx1+ inctx) = inctx
  shift-helper {Γ2 = x , Γ2} neq InCtxZ = InCtxZ
  shift-helper {Γ2 = x , Γ2} neq (InCtx1+ inctx) = InCtx1+ (shift-helper (h1 neq) inctx)
    where 
      h1 : {a b : Nat} → (1+ a == 1+ b → ⊥) → (a == b) → ⊥ 
      h1 neq refl = neq refl

  wt-ttSub-helper : ∀{Θ Γ1 Γ2 n d1 d2 τ1 τ2} →
    (Θ ⊢ τ1 wf) → 
    (Θ , Γ1 ⊢ d1 :: τ1) → 
    (n nat+ Θ) , Γ2 ctx+ (τ1 , Γ1) ⊢ d2 :: τ2 → 
    (n nat+ Θ) , Γ2 ctx+ Γ1 ⊢ ↓d (ctx-len Γ2) 1 ([ ↑d Z (ctx-len Γ2 nat+ 1) d1 / (ctx-len Γ2) ] d2) :: τ2
  wt-ttSub-helper wf wt1 TAConst = TAConst
  wt-ttSub-helper {Γ2 = Γ2} {n = n} wf wt1 (TAVar {n = m} x) with natEQ m (ctx-len Γ2) 
  ... | Inl refl = {!   !} 
  ... | Inr neq = TAVar (shift-helper neq x)
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

  -- instruction transitions preserve type
  preserve-trans : ∀{ d d' τ } →
    Z , ∅ ⊢ d :: τ →
    d →> d' →
    Z , ∅ ⊢ d' :: τ
  preserve-trans TAConst ()
  preserve-trans (TAVar x) ()
  preserve-trans (TALam x wt) ()
  preserve-trans (TATLam wt) ()
  preserve-trans (TAAp (TALam wf wt1) wt2) ITLam = {!   !}
  preserve-trans (TAAp (TACast wt1 (WFArr wf1 wf2) (ConsistArr con1 con2)) wt2) ITApCast with wf-ta CtxWFEmpty wt1
  ... | WFArr wf3 wf4 = TACast (TAAp wt1 (TACast wt2 wf3 (~sym con1))) wf2 con2
  preserve-trans (TATAp wf (TATLam wt) refl) ITTLam = wt-TtSub wf wt
  preserve-trans (TATAp x (TACast wt (WFForall wf) (ConsistForall con)) refl) ITTApCast with wf-ta CtxWFEmpty wt 
  ... | WFForall wt2 = TACast (TATAp x wt refl) (wf-TTSub x wf) (~TTSub x wt2 wf con)
  preserve-trans (TAEHole _) () 
  preserve-trans (TANEHole _ _) ()
  preserve-trans (TACast wt x x₁) ITCastID = wt
  preserve-trans (TACast (TACast wt x₃ x₄) x x₁) (ITCastSucceed gnd) = wt
  preserve-trans (TACast (TACast wt x₅ x₆) x x₁) (ITCastFail gnd x₃ x₄) = TAFailedCast wt gnd x₃ x₄
  preserve-trans (TACast wt x x₁) (ITGround (MGArr x₂)) = TACast (TACast wt (WFArr x x) (ConsistArr ConsistHole1 ConsistHole1)) x ConsistHole1
  preserve-trans (TACast wt x x₁) (ITGround (MGForall x₂)) = TACast (TACast wt (WFForall WFHole) (ConsistForall ConsistHole1)) x ConsistHole1
  preserve-trans (TACast wt x x₁) (ITExpand (MGArr x₂)) = TACast (TACast wt (WFArr WFHole WFHole) ConsistHole2) x (ConsistArr ConsistHole2 ConsistHole2)
  preserve-trans (TACast wt x x₁) (ITExpand (MGForall x₂)) = TACast (TACast wt (WFForall WFHole) ConsistHole2) x (ConsistForall ConsistHole2)
  preserve-trans (TAFailedCast wt x x₁ x₂) ()  

  -- evaluation steps preserve type
  preservation : ∀ { d d' τ } →  
    Z , ∅ ⊢ d :: τ → 
    d ↦ d' →
    Z , ∅ ⊢ d' :: τ    
  preservation wt (Step fill1 trans fill2) with wt-filling wt fill1       
  ... | τ' , wt' = wt-different-fill fill1 fill2 wt wt' (preserve-trans wt' trans) 