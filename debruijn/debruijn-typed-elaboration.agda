open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet

module debruijn.debruijn-typed-elaboration where

  mutual

    typed-elaboration-ana-prec : ∀{Γ e τ τ' d Θ} →
      Θ ⊢ Γ ctxwf → 
      Θ ⊢ τ wf → 
      Θ , Γ ⊢ e ⇐ τ ~> d :: τ' →
      τ' ⊑t τ
    typed-elaboration-ana-prec ctxwf wf (EALam MAHole ana) = PTHole
    typed-elaboration-ana-prec ctxwf (WFArr wf wf₁) (EALam MAArr ana) = PTArr (⊑t-refl _) (typed-elaboration-ana-prec (CtxWFExtend wf ctxwf) wf₁ ana)
    typed-elaboration-ana-prec ctxwf wf (EATLam neq1 neq2 MFHole ana) = PTHole
    typed-elaboration-ana-prec ctxwf (WFForall wf) (EATLam neq1 neq2 MFForall ana) = PTForall (typed-elaboration-ana-prec (weakening-ctx ctxwf) wf ana)
    typed-elaboration-ana-prec ctxwf wf (EASubsume neq1 neq2 xsyn meet) = π1 (⊓-lb meet)
    typed-elaboration-ana-prec ctxwf wf EAEHole = ⊑t-refl _
    typed-elaboration-ana-prec ctxwf wf (EANEHole x) = ⊑t-refl _

    typed-elaboration-syn : ∀{Γ e τ d Θ} →
      (Θ ⊢ Γ ctxwf) → 
      (Θ , Γ ⊢ e ⇒ τ ~> d) →
      (Θ , Γ ⊢ d :: τ)
    typed-elaboration-syn ctxwf ESConst = TAConst
    typed-elaboration-syn ctxwf (ESVar x) = TAVar x
    typed-elaboration-syn ctxwf (ESLam x syn) = TALam x (typed-elaboration-syn (CtxWFExtend x ctxwf) syn)
    typed-elaboration-syn ctxwf (ESTLam syn) = TATLam (typed-elaboration-syn (weakening-ctx ctxwf) syn)
    typed-elaboration-syn ctxwf (ESAp syn match ana1 ana2) with wf-▸arr match (wf-syn ctxwf syn)
    ... | wf1 , wf2 = TAAp (TACast (typed-elaboration-ana ctxwf (WFArr wf1 wf2) ana1) (WFArr wf1 wf2) (⊑t-consist (typed-elaboration-ana-prec {!   !} {!   !} ana1))) {!   !}
    typed-elaboration-syn ctxwf (ESTAp x x₁ x₂ x₃ x₄) = {!   !}
    typed-elaboration-syn ctxwf ESEHole = {!   !}
    typed-elaboration-syn ctxwf (ESNEHole syn) = {!   !}
    typed-elaboration-syn ctxwf (ESAsc x x₁) = {!   !}

    typed-elaboration-ana : ∀{Γ e τ τ' d Θ} →
      Θ ⊢ Γ ctxwf → 
      Θ ⊢ τ wf → 
      Θ , Γ ⊢ e ⇐ τ ~> d :: τ' →
      Θ , Γ ⊢ d :: τ'
    typed-elaboration-ana = {!   !}
    