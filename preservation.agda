open import Prelude
open import core-type
open import core

open import lemmas-consistency
open import lemmas-wf
open import lemmas-subst
open import typing-subst

open import type-assignment-unicity

module preservation where

  wt-filling : ∀{ ε Γ d τ d' } →
    Γ ⊢ d :: τ →
    d == ε ⟦ d' ⟧ →
    Σ[ τ' ∈ htyp ] (Γ ⊢ d' :: τ')
  wt-filling wt FHOuter = _ , wt
  wt-filling (TAAp wt _) (FHAp1 fill) = wt-filling wt fill 
  wt-filling (TAAp _ wt) (FHAp2 fill) = wt-filling wt fill
  wt-filling (TATAp _ wt _) (FHTAp fill) = wt-filling wt fill
  wt-filling (TANEHole wt) (FHNEHole fill) = wt-filling wt fill
  wt-filling (TACast wt _ _) (FHCast fill) = wt-filling wt fill
  wt-filling (TAFailedCast wt _ _ _) (FHFailedCast fill) = wt-filling wt fill

  wt-different-fill : ∀{ Γ d ε d1 d2 d' τ1 τ2} →
    d == ε ⟦ d1 ⟧ →
    d' == ε ⟦ d2 ⟧ →
    Γ ⊢ d :: τ1 →
    Γ ⊢ d1 :: τ2 →
    Γ ⊢ d2 :: τ2 →
    Γ ⊢ d' :: τ1
  wt-different-fill FHOuter FHOuter wt wt2 wt3 rewrite type-assignment-unicity wt wt2 = wt3
  wt-different-fill (FHAp1 fill1) (FHAp1 fill2) (TAAp wt wt1) wt2 wt3 = TAAp (wt-different-fill fill1 fill2 wt wt2 wt3) wt1
  wt-different-fill (FHAp2 fill1) (FHAp2 fill2) (TAAp wt wt1) wt2 wt3 = TAAp wt (wt-different-fill fill1 fill2 wt1 wt2 wt3)
  wt-different-fill (FHTAp fill1) (FHTAp fill2) (TATAp x wt sub) wt2 wt3 = TATAp x (wt-different-fill fill1 fill2 wt wt2 wt3) sub
  wt-different-fill (FHNEHole fill1) (FHNEHole fill2) (TANEHole wt) wt2 wt3 = TANEHole (wt-different-fill fill1 fill2 wt wt2 wt3)
  wt-different-fill (FHCast fill1) (FHCast fill2) (TACast wt wf con) wt2 wt3 = TACast (wt-different-fill fill1 fill2 wt wt2 wt3) wf con
  wt-different-fill (FHFailedCast fill1) (FHFailedCast fill2) (TAFailedCast wt gnd1 gnd2 incon) wt2 wt3 = TAFailedCast (wt-different-fill fill1 fill2 wt wt2 wt3) gnd1 gnd2 incon

  -- instruction transitions preserve type
  preserve-trans : ∀{ d d' τ } →
    ∅ ⊢ d :: τ →
    d →> d' →
    ∅ ⊢ d' :: τ
  preserve-trans TAConst ()
  preserve-trans (TAVar x) ()
  preserve-trans (TALam x wt) ()
  preserve-trans (TATLam wt) ()
  preserve-trans (TAAp (TALam wf wt1) wt2) ITLam = wt-ttSub wt2 wt1
  preserve-trans (TAAp (TACast wt1 (WFArr _ wf1) (ConsistArr con1 con2)) wt2) ITApCast with wf-ta CtxWFEmpty wt1
  ... | WFArr wf2 _ = TACast (TAAp wt1 (TACast wt2 wf2 (~sym con1))) wf1 con2
  preserve-trans (TATAp wf (TATLam wt) refl) ITTLam = wt-TtSub wf wt
  preserve-trans (TATAp wf1 (TACast wt (WFForall wf2) (ConsistForall con)) refl) ITTApCast with wf-ta CtxWFEmpty wt 
  ... | WFForall wf3 = TACast (TATAp wf1 wt refl) (wf-TTSub wf1 wf2) (~TTSub wf3 wf2 con)
  preserve-trans TAEHole () 
  preserve-trans (TANEHole _) ()
  preserve-trans (TACast wt _ _) ITCastID = wt
  preserve-trans (TACast (TACast wt _ _) _ _) (ITCastSucceed gnd) = wt
  preserve-trans (TACast (TACast wt _ _) _ _) (ITCastFail gnd1 gnd2 incon) = TAFailedCast wt gnd1 gnd2 incon
  preserve-trans (TACast wt wf _) (ITGround (MGArr _)) = TACast (TACast wt (WFArr wf wf) (ConsistArr ConsistHole1 ConsistHole1)) wf ConsistHole1
  preserve-trans (TACast wt wf _) (ITGround (MGForall _)) = TACast (TACast wt (WFForall WFHole) (ConsistForall ConsistHole1)) wf ConsistHole1
  preserve-trans (TACast wt wf _) (ITExpand (MGArr _)) = TACast (TACast wt (WFArr WFHole WFHole) ConsistHole2) wf (ConsistArr ConsistHole2 ConsistHole2)
  preserve-trans (TACast wt wf _) (ITExpand (MGForall _)) = TACast (TACast wt (WFForall WFHole) ConsistHole2) wf (ConsistForall ConsistHole2)
  preserve-trans (TAFailedCast _ _ _ _) ()  

  -- evaluation steps preserve type
  preservation : ∀ { d d' τ } →  
    ∅ ⊢ d :: τ →
    d ↦ d' →
    ∅ ⊢ d' :: τ
  preservation wt (Step fill1 trans fill2) with wt-filling wt fill1       
  ... | _ , wt' = wt-different-fill fill1 fill2 wt wt' (preserve-trans wt' trans) 
 