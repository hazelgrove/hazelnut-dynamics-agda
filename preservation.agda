open import Nat
open import Prelude
open import List
open import core
open import contexts

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
  pres-lem (FHAp1 eps) D1 D2 D3 (FHAp1 D4) = {!!}
  pres-lem (FHAp2 x eps) D1 D2 D3 (FHAp2 x₁ D4) = {!!}
  pres-lem (FHNEHole eps) D1 D2 D3 (FHNEHole D4) = {!!}
  pres-lem (FHCast eps) D1 D2 D3 (FHCast D4) = {!!}

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
  pres-lem2 (TAAp ta ta₁) (FHAp2 x eps) = pres-lem2 ta₁ eps

  pres-lem2 (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  pres-lem2 (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  pres-lem2 (TANEHole x ta x₁) (FHNEHole eps) = pres-lem2 ta eps
  pres-lem2 (TACast ta x) FHOuter = _ , TACast ta x
  pres-lem2 (TACast ta x) (FHCast eps) = pres-lem2 ta eps

  -- todo: rename
  pres-lem3 : ∀{ Δ Γ d τ d' } →
            Δ , Γ ⊢ d :: τ →
            d →> d' →
            Δ , Γ ⊢ d' :: τ
  pres-lem3 TAConst ()
  pres-lem3 (TAVar x₁) ()
  pres-lem3 (TALam ta) ()
  pres-lem3 (TAAp ta ta₁) (ITLam x₁) = {!!}
  pres-lem3 (TAAp ta ta₁) (ITApCast x x₁) = {!!}
  pres-lem3 (TAEHole x x₁) ()
  pres-lem3 (TANEHole x ta x₁) () -- todo: this is a little surprising; nehole doesn't take a transition but it defieately can still step
  pres-lem3 (TACast ta x) (ITCastID x₁) = {!!}
  pres-lem3 (TACast ta x) (ITCastSucceed x₁ x₂) = {!!}
  pres-lem3 (TACast ta x) (ITGround x₁ y) = {!!}
  pres-lem3 (TACast ta x) (ITExpand x₁ x₂) = {!!}

  preservation : {Δ : hctx} {d d' : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  preservation D (Step x x₁ x₂)
    with pres-lem2 D x
  ... | (_ , wt) = pres-lem x D wt (pres-lem3 wt x₁) x₂
