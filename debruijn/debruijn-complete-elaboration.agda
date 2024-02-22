open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-complete

module debruijn.debruijn-complete-elaboration where

  comp-synth : ∀{Γ e τ} →
    Γ gcomplete →
    e ecomplete →
    Γ ⊢ e => τ →
    τ tcomplete
  comp-synth gc ECConst SConst = TCBase
  comp-synth gc (ECAsc x ec) (SAsc x₁ x₂) = x
  comp-synth gc ECVar (SVar x) = inctx-complete gc x
  comp-synth gc (ECLam1 ec) ()
  comp-synth gc (ECLam2 ec x) (SLam x₁ syn) = TCArr x (comp-synth (GCVar gc x) ec syn)
  comp-synth gc (ECTLam ec) (STLam syn) = TCForall (comp-synth (GCTVar gc) ec syn)
  comp-synth gc (ECAp ec ec₁) (SAp syn meet x₁) with meet-complete (comp-synth gc ec syn) meet
  ... | TCArr tc tc₁ = tc₁
  comp-synth gc (ECTAp x ec) (STAp x₁ syn meet refl) with meet-complete (comp-synth gc ec syn) meet 
  ... | TCForall tc = TTSub-complete x tc


  mutual
    complete-elaboration-synth : ∀{e τ Γ d} →
      Γ gcomplete →
      e ecomplete →
      Γ ⊢ e ⇒ τ ~> d →
      (d dcomplete × τ tcomplete)

    complete-elaboration-synth gc ec ESConst = DCConst , TCBase 
    complete-elaboration-synth gc ec (ESVar inctx) = DCVar , inctx-complete gc inctx
    complete-elaboration-synth gc (ECLam2 ec tc) (ESLam wf elab) with complete-elaboration-synth (GCVar gc tc) ec elab 
    ... | dc' , tc' = (DCLam dc' tc) , TCArr tc tc'
    complete-elaboration-synth gc (ECAp ec ec₁) (ESAp syn meet ana1 ana2) with meet-complete (comp-synth gc ec syn) meet
    ... | TCArr tc1 tc2 with complete-elaboration-ana gc ec (TCArr tc1 tc2) ana1 
    ... | dc' , tc' with complete-elaboration-ana gc ec₁ tc1 ana2
    ... | dc'' , tc'' = (DCAp (DCCast dc' tc' (TCArr tc1 tc2)) (DCCast dc'' tc'' tc1)) , tc2
    complete-elaboration-synth gc () ESEHole
    complete-elaboration-synth gc () (ESNEHole exp)
    complete-elaboration-synth gc (ECAsc x ec) (ESAsc wf x₁)
      with complete-elaboration-ana gc ec x x₁
    ... | dc' , tc' = DCCast dc' tc' x , x
    complete-elaboration-synth gc (ECTLam ec) (ESTLam elab) with complete-elaboration-synth (GCTVar gc) ec elab
    ... | dc' , tc' = DCTLam dc' , TCForall tc'
    complete-elaboration-synth gc (ECTAp ec tc) (ESTAp wf syn meet ana refl) with meet-complete (comp-synth gc tc syn) meet 
    ... | TCForall tc'' with complete-elaboration-ana gc tc (TCForall tc'') ana 
    ... | thing = (DCTAp ec (DCCast (π1 thing) (π2 thing) (TCForall tc''))) , TTSub-complete ec tc''

    complete-elaboration-ana : ∀{e τ τ' Γ d} →
      Γ gcomplete →
      e ecomplete →
      τ tcomplete →
      Γ ⊢ e ⇐ τ ~> d :: τ' →
      (d dcomplete × τ' tcomplete)
      
    complete-elaboration-ana gc (ECLam1 ec) tc (EALam meet ana) with meet-complete tc meet 
    ... | TCArr tc1 tc2 with complete-elaboration-ana (GCVar gc tc1) ec tc2 ana 
    ... | dc' , tc' = DCLam dc' tc1 , TCArr tc1 tc'
    complete-elaboration-ana gc ec tc (EASubsume x syn meet) with complete-elaboration-synth gc ec syn | meet-complete tc meet 
    ... | dc' , tc' | tc'' = DCCast dc' tc' tc'' , tc''
    complete-elaboration-ana x (ECTLam x₂) x₁ (EATLam meet ana) with meet-complete x₁ meet 
    ... | TCForall tc with complete-elaboration-ana (GCTVar x) x₂ tc ana
    ... | dc , tc' = DCTLam dc , TCForall tc'
