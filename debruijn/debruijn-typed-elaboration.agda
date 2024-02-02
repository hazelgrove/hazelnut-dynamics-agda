open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-wf

module debruijn.debruijn-typed-elaboration where

  mutual

    typed-elaboration-syn : ∀{Γ e τ d Θ} →
      (Θ ⊢ Γ ctxwf) → 
      (Θ , Γ ⊢ e ⇒ τ ~> d) →
      (Θ , Γ ⊢ d :: τ)
    typed-elaboration-syn ctxwf ESConst = TAConst
    typed-elaboration-syn ctxwf (ESVar x) = TAVar x
    typed-elaboration-syn ctxwf (ESLam x syn) = TALam x (typed-elaboration-syn (CtxWFExtend x ctxwf) syn)
    typed-elaboration-syn ctxwf (ESTLam syn) = TATLam (typed-elaboration-syn (weakening-ctx ctxwf) syn)
    typed-elaboration-syn ctxwf (ESAp syn match ana1 ana2) = TAAp (TACast (typed-elaboration-ana ctxwf (WFArr (π1 (wf-▸arr match {!   !})) {!   !}) ana1) {!   !} {!   !}) {!   !}
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