open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-wf

module debruijn.debruijn-preservation where

  wt-filling : ∀{ ε Γ d τ d' } →
    Z , Γ ⊢ d :: τ →
    d == ε ⟦ d' ⟧ →
    Σ[ τ' ∈ htyp ] (Z , Γ ⊢ d' :: τ')
  wt-filling wt fill = {!   !}

  wt-different-fill : ∀{ Γ d ε d1 d2 d' τ1 τ2} →
    d == ε ⟦ d1 ⟧ →
    d' == ε ⟦ d2 ⟧ →
    Z , Γ ⊢ d :: τ1 →
    Z , Γ ⊢ d1 :: τ2 →
    Z , Γ ⊢ d2 :: τ2 →
    Z , Γ ⊢ d' :: τ1
  wt-different-fill = {!   !}

  -- note: wf1 assumption might end up unecessary

  ~TTSub-helper : ∀{n τ1 τ2 τ3} → (n ⊢ τ1 wf) → (1+ n ⊢ τ2 wf) → (1+ n ⊢ τ3 wf) → τ2 ~ τ3 → (↓ n 1 (TT[ (↑ Z (1+ n) τ1) / n ] τ2)) ~ (↓ n 1 (TT[ (↑ Z (1+ n) τ1) / n ] τ3))
  ~TTSub-helper wf1 wf2 wf3 ConsistBase = ConsistBase
  ~TTSub-helper wf1 wf2 wf3 ConsistVar = {!   !}
  ~TTSub-helper wf1 wf2 wf3 ConsistHole1 = ConsistHole1
  ~TTSub-helper wf1 wf2 wf3 ConsistHole2 = ConsistHole2 
  ~TTSub-helper wf1 (WFArr wf2 wf3) (WFArr wf4 wf5) (ConsistArr con1 con2) = ConsistArr (~TTSub-helper wf1 wf2 wf4 con1) (~TTSub-helper wf1 wf3 wf5 con2)
  ~TTSub-helper {n = n} {τ1 = τ1} wf1 (WFForall wf2) (WFForall wf3) (ConsistForall con) with ↑compose Z (1+ n) τ1
  ...| eq rewrite eq = ConsistForall (~TTSub-helper (weakening wf1) wf2 wf3 con)

  ~TTSub : {τ1 τ2 τ3 : htyp} → Z ⊢ τ1 wf → 1 ⊢ τ2 wf → 1 ⊢ τ3 wf → τ2 ~ τ3 → TTSub τ1 τ2 ~ TTSub τ1 τ3
  ~TTSub wf1 wf2 wf3 con = ~TTSub-helper {n = Z} wf1 wf2 wf3 con

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
  preserve-trans (TATAp x (TATLam wt) refl) ITTLam = {!   !}
  preserve-trans (TATAp x (TACast wt (WFForall wf) (ConsistForall con)) refl) ITTApCast with wf-ta CtxWFEmpty wt 
  ... | WFForall wt2 = TACast (TATAp x wt refl) (wf-TTSub x wf) (~TTSub x wt2 wf con)
  preserve-trans (TAEHole _) () 
  preserve-trans (TANEHole _) ()
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