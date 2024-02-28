open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-lemmas-subst
open import debruijn.debruijn-lemmas-complete

module debruijn.debruijn-complete-preservation where

  complete-wt-filling : ∀{ ε Γ d τ d' } →
    d dcomplete →
    Γ ⊢ d :: τ →
    d == ε ⟦ d' ⟧ →
    Σ[ τ' ∈ htyp ] (Γ ⊢ d' :: τ' × d' dcomplete)
  complete-wt-filling dc wt FHOuter = _ , wt , dc
  complete-wt-filling (DCAp dc _) (TAAp wt _) (FHAp1 fill) = complete-wt-filling dc wt fill
  complete-wt-filling (DCAp _ dc) (TAAp _ wt) (FHAp2 fill) = complete-wt-filling dc wt fill
  complete-wt-filling (DCTAp _ dc) (TATAp _ wt _) (FHTAp fill) = complete-wt-filling dc wt fill
  complete-wt-filling (DCCast dc _ _) (TACast wt _ _) (FHCast fill) = complete-wt-filling dc wt fill

  complete-wt-different-fill : ∀{d ε d1 d2 d'} →
    d dcomplete → 
    d2 dcomplete → 
    d == ε ⟦ d1 ⟧ →
    d' == ε ⟦ d2 ⟧ →
    d' dcomplete
  complete-wt-different-fill dc1 dc2 FHOuter FHOuter = dc2
  complete-wt-different-fill (DCAp dc1 dc3) dc2 (FHAp1 fill1) (FHAp1 fill2) = DCAp (complete-wt-different-fill dc1 dc2 fill1 fill2) dc3
  complete-wt-different-fill (DCAp dc1 dc3) dc2 (FHAp2 fill1) (FHAp2 fill2) = DCAp dc1 (complete-wt-different-fill dc3 dc2 fill1 fill2)
  complete-wt-different-fill (DCTAp tc dc1) dc2 (FHTAp fill1) (FHTAp fill2) = DCTAp tc (complete-wt-different-fill dc1 dc2 fill1 fill2)
  complete-wt-different-fill (DCCast dc1 tc1 tc2) dc2 (FHCast fill1) (FHCast fill2) = DCCast (complete-wt-different-fill dc1 dc2 fill1 fill2) tc1 tc2

  complete-preservation-trans : ∀{d τ d'} →
    d dcomplete →
    ∅ ⊢ d :: τ →
    d →> d' →
    d' dcomplete
  complete-preservation-trans _ TAConst ()
  complete-preservation-trans _ TAEHole ()
  complete-preservation-trans _ (TAVar _) ()
  complete-preservation-trans _ (TALam _ _) ()
  complete-preservation-trans _ (TATLam _) ()  
  complete-preservation-trans _ (TANEHole _) ()
  complete-preservation-trans (DCCast dc _ _) _ ITCastID = dc
  complete-preservation-trans (DCCast _ () _) _ (ITCastSucceed _)
  complete-preservation-trans (DCCast _ () _) _ (ITCastFail _ _ _) 
  complete-preservation-trans (DCCast _ _ ()) _ (ITGround _)
  complete-preservation-trans (DCCast _ () _) _ (ITExpand _)
  complete-preservation-trans _ (TAFailedCast _ _ _ _) ()
  complete-preservation-trans (DCTAp tc (DCTLam dc)) _ ITTLam = TtSub-complete tc dc
  complete-preservation-trans (DCAp (DCLam dc1 _) dc2) _ ITLam = ttSub-complete dc2 dc1
  complete-preservation-trans (DCAp (DCCast dc1 (TCArr tc1 tc2) (TCArr tc3 tc4)) dc2) _ ITApCast = DCCast (DCAp dc1 (DCCast dc2 tc3 tc1)) tc2 tc4
  complete-preservation-trans (DCTAp tc1 (DCCast dc (TCForall tc2) (TCForall tc3))) _ ITTApCast = DCCast (DCTAp tc1 dc) (TTSub-complete tc1 tc2) (TTSub-complete tc1 tc3)

  complete-preservation : ∀{d τ d'} →
    d dcomplete →
    ∅ ⊢ d :: τ → 
    d ↦ d' → 
    d' dcomplete
  complete-preservation dc wt (Step fill1 trans fill2) with complete-wt-filling dc wt fill1       
  ... | _ , wt' , dc' = complete-wt-different-fill dc (complete-preservation-trans dc' wt' trans) fill1 fill2