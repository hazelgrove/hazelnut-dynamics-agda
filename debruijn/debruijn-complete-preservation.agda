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
  complete-wt-filling (DCAp dc dc₁) (TAAp wt wt₁) (FHAp1 fill) = complete-wt-filling dc wt fill
  complete-wt-filling (DCAp _ dc) (TAAp _ wt) (FHAp2 fill) = complete-wt-filling dc wt fill
  complete-wt-filling (DCTAp x dc) (TATAp x₁ wt x₂) (FHTAp fill) = complete-wt-filling dc wt fill
  complete-wt-filling (DCCast dc x x₁) (TACast wt x₂ x₃) (FHCast fill) = complete-wt-filling dc wt fill

  complete-wt-different-fill : ∀{d ε d1 d2 d'} →
    d dcomplete → 
    d2 dcomplete → 
    d == ε ⟦ d1 ⟧ →
    d' == ε ⟦ d2 ⟧ →
    d' dcomplete
  complete-wt-different-fill dc1 dc2 FHOuter FHOuter = dc2
  complete-wt-different-fill (DCAp dc1 dc3) dc2 (FHAp1 fill1) (FHAp1 fill2) = DCAp (complete-wt-different-fill dc1 dc2 fill1 fill2) dc3
  complete-wt-different-fill (DCAp dc1 dc3) dc2 (FHAp2 fill1) (FHAp2 fill2) = DCAp dc1 (complete-wt-different-fill dc3 dc2 fill1 fill2)
  complete-wt-different-fill (DCTAp x dc1) dc2 (FHTAp fill1) (FHTAp fill2) = DCTAp x (complete-wt-different-fill dc1 dc2 fill1 fill2)
  complete-wt-different-fill (DCCast dc1 x x₁) dc2 (FHCast fill1) (FHCast fill2) = DCCast (complete-wt-different-fill dc1 dc2 fill1 fill2) x x₁

  complete-preservation-trans : ∀{d τ d'} →
    d dcomplete →
    ∅ ⊢ d :: τ →
    d →> d' →
    d' dcomplete
  complete-preservation-trans dc TAConst ()
  complete-preservation-trans dc (TAVar x) ()
  complete-preservation-trans dc (TALam x ta) ()
  complete-preservation-trans dc (TATLam ta) ()
  complete-preservation-trans (DCAp (DCLam dc x) dc₁) (TAAp ta ta₁) ITLam = ttSub-complete dc₁ dc 
  complete-preservation-trans (DCAp (DCCast dc (TCArr x x₃) (TCArr x₁ x₂)) dc₁) (TAAp (TACast ta (WFArr x₄ x₇) (ConsistArr x₅ x₆)) ta₁) ITApCast = DCCast (DCAp dc (DCCast dc₁ x₁ x)) x₃ x₂
  complete-preservation-trans (DCTAp x₂ (DCTLam dc)) (TATAp x (TATLam ta) x₁) ITTLam = TtSub-complete x₂ dc
  complete-preservation-trans (DCTAp x₂ (DCCast dc (TCForall tc) (TCForall tc'))) (TATAp x (TACast ta (WFForall x₅) (ConsistForall x₆)) x₁) ITTApCast = DCCast (DCTAp x₂ dc) (TTSub-complete x₂ tc) (TTSub-complete x₂ tc')
  complete-preservation-trans dc TAEHole ()
  complete-preservation-trans dc (TANEHole ta) ()
  complete-preservation-trans (DCCast dc x₂ x₃) (TACast ta x x₁) ITCastID = dc
  complete-preservation-trans (DCCast _ () _) (TACast ta x x₁) (ITCastSucceed x₂)
  complete-preservation-trans (DCCast _ () _) (TACast ta x x₁) (ITCastFail x₂ x₃ x₄) 
  complete-preservation-trans (DCCast _ _ ()) (TACast ta x x₁) (ITGround x₂)
  complete-preservation-trans (DCCast _ () _) (TACast ta x x₁) (ITExpand x₂)
  complete-preservation-trans dc (TAFailedCast ta x x₁ x₂) ()

  complete-preservation : ∀{d τ d'} →
    d dcomplete →
    ∅ ⊢ d :: τ → 
    d ↦ d' → 
    d' dcomplete
  complete-preservation dc wt (Step fill1 trans fill2) with complete-wt-filling dc wt fill1       
  ... | τ' , wt' , dc' = complete-wt-different-fill dc (complete-preservation-trans dc' wt' trans) fill1 fill2