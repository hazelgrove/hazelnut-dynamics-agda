open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-typed-elaboration
open import debruijn.debruijn-type-assignment-unicity

module debruijn.debruijn-preci-trans where 

  ⊑i-trans : ∀{Θ Γ1 Γ2 Γ3 d1 d2 d3} → Γ1 ⊑c Γ2 → Γ2 ⊑c Γ3 → Θ , Γ1 , Γ2 ⊢ d1 ⊑i d2 → Θ , Γ2 , Γ3 ⊢ d2 ⊑i d3 → Θ , Γ1 , Γ3 ⊢ d1 ⊑i d3
  ⊑i-trans precc1 precc2 prec1 (PIEHole wt prec2) = PIEHole {!   !} {!   !}
  ⊑i-trans precc1 precc2 (PIBlame TAConst PTBase) PIConst = PIBlame TAConst PTBase
  ⊑i-trans precc1 precc2 (PIBlame (TAVar inctx) prec) PIVar with ⊑c-var inctx precc2 
  ... | τ , inctx' , prec' = PIBlame (TAVar inctx') (⊑t-trans prec prec')
  ⊑i-trans precc1 precc2 (PIBlame (TALam x₁ wt) prec1) (PILam prec2 x) = PIBlame (TALam (wf-⊑t x₁ x) {!   !}) {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PITLam prec2) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PINEHole prec2 x) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIAp prec2 prec3) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PITAp prec2 x) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PICast prec2 x x₁) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIFailedCast prec2 x x₁) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIRemoveCast prec2 x x₁ x₂) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIAddCast prec2 x x₁ x₂) = {!   !}
  ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIBlame x x₁) = {!   !} 
  ⊑i-trans precc1 precc2 PIConst PIConst = {!   !}
  ⊑i-trans precc1 precc2 (PIRemoveCast prec1 x x₁ x₂) PIConst = {!   !}
  ⊑i-trans precc1 precc2 prec1 PIVar = {!   !} 
  ⊑i-trans precc1 precc2 (PILam prec1 prec2) (PILam prec3 prec4) = PILam (⊑i-trans (PCExtend prec2 precc1) (PCExtend prec4 precc2) prec1 prec3) (⊑t-trans prec2 prec4)
  ⊑i-trans precc1 precc2 (PIRemoveCast prec1 x₁ x₂ x₃) (PILam prec2 x) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PITLam prec2) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PINEHole prec2 x) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PIAp prec2 prec3) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PITAp prec2 x) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PICast prec2 x x₁) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PIFailedCast prec2 x x₁) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PIRemoveCast prec2 x x₁ x₂) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PIAddCast prec2 x x₁ x₂) = {!   !}
  ⊑i-trans precc1 precc2 prec1 (PIBlame x x₁) = {!   !}