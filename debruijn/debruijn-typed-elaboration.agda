open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet

module debruijn.debruijn-typed-elaboration where

  ⊑t-ana : ∀{Γ e τ τ' d Θ} →
    Θ ⊢ Γ ctxwf → 
    Θ ⊢ τ wf → 
    Θ , Γ ⊢ e ⇐ τ ~> d :: τ' →
    τ' ⊑t τ
  ⊑t-ana ctxwf wf (EALam meet ana) with ⊓-lb meet 
  ... | PTHole , _ = PTHole
  ... | PTArr prec1 prec2 , _ with wf-⊓ meet wf (WFArr WFHole WFHole)
  ... | WFArr wf1 wf2 = PTArr prec1 (⊑t-trans (⊑t-ana (CtxWFExtend wf1 ctxwf) wf2 ana) prec2)
  ⊑t-ana ctxwf wf (EATLam neq1 neq2 meet ana) with ⊓-lb meet 
  ... | PTHole , _ = PTHole
  ... | PTForall prec1 , _ with wf-⊓ meet wf (WFForall WFHole)
  ... | WFForall wf1 = PTForall (⊑t-trans (⊑t-ana (weakening-ctx ctxwf) wf1 ana) prec1)
  ⊑t-ana ctxwf wf (EASubsume neq1 neq2 xsyn meet) = π1 (⊓-lb meet)
  ⊑t-ana ctxwf wf EAEHole = ⊑t-refl _
  ⊑t-ana ctxwf wf (EANEHole x) = ⊑t-refl _

  consist-ana : ∀{Γ e τ τ' d Θ} →
    Θ ⊢ Γ ctxwf → 
    Θ ⊢ τ wf → 
    Θ , Γ ⊢ e ⇐ τ ~> d :: τ' →
    τ' ~ τ
  consist-ana ctxwf wf ana = ⊑t-consist (⊑t-ana ctxwf wf ana)

  mutual 

    typed-elaboration-syn : ∀{Γ e τ d Θ} →
      (Θ ⊢ Γ ctxwf) → 
      (Θ , Γ ⊢ e ⇒ τ ~> d) →
      (Θ , Γ ⊢ d :: τ)
    typed-elaboration-syn ctxwf ESConst = TAConst
    typed-elaboration-syn ctxwf (ESVar x) = TAVar x
    typed-elaboration-syn ctxwf (ESLam x syn) = TALam x (typed-elaboration-syn (CtxWFExtend x ctxwf) syn)
    typed-elaboration-syn ctxwf (ESTLam syn) = TATLam (typed-elaboration-syn (weakening-ctx ctxwf) syn)
    typed-elaboration-syn ctxwf (ESAp syn meet ana1 ana2) with ⊓-lb meet | wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
    ... | prec1 , prec2 | WFArr wf1 wf2 = 
      TAAp (TACast (typed-elaboration-ana ctxwf (WFArr wf1 wf2) ana1) (WFArr wf1 wf2) (consist-ana ctxwf (WFArr wf1 wf2) ana1)) 
      ((TACast (typed-elaboration-ana ctxwf wf1 ana2) wf1 (consist-ana ctxwf wf1 ana2)))
    typed-elaboration-syn ctxwf (ESTAp wf syn meet ana refl) = 
      let wf' = wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole) in 
      TATAp wf (TACast (typed-elaboration-ana ctxwf wf' ana) wf' (consist-ana ctxwf wf' ana)) refl
    typed-elaboration-syn ctxwf ESEHole = TAEHole
    typed-elaboration-syn ctxwf (ESNEHole syn) = TANEHole
    typed-elaboration-syn ctxwf (ESAsc wf ana) = TACast (typed-elaboration-ana ctxwf wf ana) wf (consist-ana ctxwf wf ana)

    typed-elaboration-ana : ∀{Γ e τ τ' d Θ} →
      Θ ⊢ Γ ctxwf → 
      Θ ⊢ τ wf → 
      Θ , Γ ⊢ e ⇐ τ ~> d :: τ' →
      Θ , Γ ⊢ d :: τ'
    typed-elaboration-ana ctxwf wf EAEHole = TAEHole
    typed-elaboration-ana ctxwf wf (EANEHole x) = TANEHole
    typed-elaboration-ana ctxwf wf (EALam meet ana) with wf-⊓ meet wf (WFArr WFHole WFHole) 
    ... | WFArr wf1 wf2 = TALam wf1 (typed-elaboration-ana (CtxWFExtend wf1 ctxwf) wf2 ana)
    typed-elaboration-ana ctxwf wf (EATLam neq1 neq2 meet ana) with wf-⊓ meet wf (WFForall WFHole) 
    ... | WFForall wf' = TATLam (typed-elaboration-ana (weakening-ctx ctxwf) wf' ana)
    typed-elaboration-ana ctxwf wf (EASubsume neq1 neq2 syn meet) = 
        TACast (typed-elaboration-syn ctxwf syn) (wf-⊓ meet wf (wf-elab-syn ctxwf syn)) (~sym (⊑t-consist (π2 (⊓-lb meet))))
    