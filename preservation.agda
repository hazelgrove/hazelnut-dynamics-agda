open import Nat
open import Prelude
open import List
open import core
open import contexts

open import lemmas-consistency
open import type-assignment-unicity

module preservation where
  -- todo: rename
  pres-lem : ∀{ Δ Γ d ε d1 d2 d3 τ τ1 } →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ ⊢ d :: τ →
            Δ , Γ ⊢ d1 :: τ1 →
            Δ , Γ ⊢ d2 :: τ1 →
            d3 == ε ⟦ d2 ⟧ →
            Δ , Γ ⊢ d3 :: τ
  pres-lem FHOuter D1 D2 D3 FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = D3
  pres-lem (FHAp1 eps) D1 D2 D3 (FHAp1 D4) = TAAp {!!} {!!}
  pres-lem (FHAp2 eps) D1 D2 D3 (FHAp2 D4) = TAAp {!!} {!!}
  pres-lem (FHNEHole eps) D1 D2 D3 (FHNEHole D4) = TANEHole {!!} {!!} {!!}
  pres-lem (FHCast eps) D1 D2 D3 (FHCast D4) = {!!}
  pres-lem (FHFailedCast eps) D1 D2 D3 (FHFailedCast D4) = {!!}

  -- todo: rename
  pres-lem2 : ∀{ ε Δ Γ d τ d' } →
             Δ , Γ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ htyp ] (Δ , Γ ⊢ d' :: τ')
  pres-lem2 TAConst FHOuter = _ , TAConst
  pres-lem2 (TAVar x₁) FHOuter = _ , TAVar x₁
  pres-lem2 (TALam ta) FHOuter = _ , TALam ta

  pres-lem2 (TAAp ta ta₁) FHOuter = _ , TAAp ta ta₁
  pres-lem2 (TAAp ta ta₁) (FHAp1 eps) = pres-lem2 ta eps
  pres-lem2 (TAAp ta ta₁) (FHAp2 eps) = pres-lem2 ta₁ eps

  pres-lem2 (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  pres-lem2 (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  pres-lem2 (TANEHole x ta x₁) (FHNEHole eps) = pres-lem2 ta eps
  pres-lem2 (TACast ta x) FHOuter = _ , TACast ta x
  pres-lem2 (TACast ta x) (FHCast eps) = pres-lem2 ta eps
  pres-lem2 (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  pres-lem2 (TAFailedCast x y z w) (FHFailedCast FHOuter) = _ , TACast x TCHole1
  pres-lem2 (TAFailedCast x y z w) (FHFailedCast (FHCast eps)) = pres-lem2 x eps

  -- todo: rename
  pres-lem3 : ∀{ Δ Γ d τ d' } →
            Δ , Γ ⊢ d :: τ →
            d →> d' →
            Δ , Γ ⊢ d' :: τ
  pres-lem3 TAConst ()
  pres-lem3 (TAVar x₁) ()
  pres-lem3 (TALam ta) ()
  pres-lem3 (TAAp (TALam ta) ta₁) ITLam = {!!} -- todo: this is a lemma
  pres-lem3 (TAAp (TACast ta TCRefl) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ TCRefl)) TCRefl
  pres-lem3 (TAAp (TACast ta (TCArr x x₁)) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ (~sym x))) x₁
  pres-lem3 (TAEHole x x₁) ()
  pres-lem3 (TANEHole x ta x₁) ()
  pres-lem3 (TACast ta x) (ITCastID) = ta
  pres-lem3 (TACast (TACast ta x) x₁) (ITCastSucceed x₂) = ta
  pres-lem3 (TACast ta x) (ITGround (MGArr x₁)) = TACast (TACast ta (TCArr TCHole1 TCHole1)) TCHole1
  pres-lem3 (TACast ta TCHole2) (ITExpand (MGArr x₁)) = TACast (TACast ta TCHole2) (TCArr TCHole2 TCHole2)
  pres-lem3 (TACast (TACast ta x) x₁) (ITCastFail w y z) = TAFailedCast ta w y z
  pres-lem3 (TAFailedCast x y z q) ()

  preservation : {Δ : hctx} {d d' : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  preservation D (Step x x₁ x₂)
    with pres-lem2 D x
  ... | (_ , wt) = pres-lem x D wt (pres-lem3 wt x₁) x₂
