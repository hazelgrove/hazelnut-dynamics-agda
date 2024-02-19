open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-lemmas-subst
open import debruijn.debruijn-typing-subst
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

  -- instruction transitions preserve type
  preserve-trans : ∀{ d d' τ } →
    Z , ∅ ⊢ d :: τ →
    d →> d' →
    Z , ∅ ⊢ d' :: τ
  preserve-trans TAConst ()
  preserve-trans (TAVar x) ()
  preserve-trans (TALam x wt) ()
  preserve-trans (TATLam wt) ()
  preserve-trans (TAAp (TALam wf wt1) wt2) ITLam = wt-ttSub wf wt2 wt1
  preserve-trans (TAAp (TACast wt1 (WFArr wf1 wf2) (ConsistArr con1 con2)) wt2) ITApCast with wf-ta CtxWFEmpty wt1
  ... | WFArr wf3 wf4 = TACast (TAAp wt1 (TACast wt2 wf3 (~sym con1))) wf2 con2
  preserve-trans (TATAp wf (TATLam wt) refl) ITTLam = wt-TtSub CtxWFEmpty wf wt
  preserve-trans (TATAp x (TACast wt (WFForall wf) (ConsistForall con)) refl) ITTApCast with wf-ta CtxWFEmpty wt 
  ... | WFForall wf2 = TACast (TATAp x wt refl) (wf-TTSub x wf) (~TTSub wf2 wf con)
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