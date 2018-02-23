open import Nat
open import Prelude
open import List
open import core
open import contexts

open import htype-decidable
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
  pres-lem (FHAp1 eps) (TAAp D1 D2) D3 D4 (FHAp1 D5) = TAAp (pres-lem eps D1 D3 D4 D5) D2
  pres-lem (FHAp2 eps) (TAAp D1 D2) D3 D4 (FHAp2 D5) = TAAp D1 (pres-lem eps D2 D3 D4 D5)
  pres-lem (FHNEHole eps) (TANEHole x D1 x₁) D2 D3 (FHNEHole D4) = TANEHole x (pres-lem eps D1 D2 D3 D4) x₁
  pres-lem (FHCast eps) (TACast D1 x) D2 D3 (FHCast D4) = TACast (pres-lem eps D1 D2 D3 D4) x
  pres-lem (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 (FHFailedCast eps) = TAFailedCast (pres-lem x y D3 D4 eps) x₁ x₂ x₃

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
  pres-lem2 (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = pres-lem2 x y

  -- this is the literal contents of the hole in lem3; it might not go
  -- through exactly like this.
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } →
              Δ , Γ ,, (x , τ1) ⊢ d1 :: τ →
              Δ , Γ ⊢ d2 :: τ1 →
              Δ , Γ ⊢ [ d2 / x ] d1 :: τ
  lem-subst TAConst D2 = TAConst
  lem-subst {Γ = Γ} {x = x'} (TAVar {x = x} x₂) D2
    with Γ x
  lem-subst {x = x} (TAVar {x = x'} x₃) D2 | Some x₁
    with natEQ x' x
  lem-subst (TAVar xin) D2 | Some x₃ | Inl refl = {!!}
  lem-subst (TAVar refl) D2 | Some x₃ | Inr x₂ = {!!}
  lem-subst {x = x} (TAVar {x = x'} x₂) D2 | None with natEQ x' x
  lem-subst {x = x} (TAVar x₃) D2 | None | Inl refl with natEQ x x
  lem-subst (TAVar refl) D2 | None | Inl refl | Inl refl = D2
  lem-subst (TAVar x₃) D2 | None | Inl refl | Inr x₁ = abort (somenotnone (! x₃))
  lem-subst {x = x} (TAVar {x = x'} x₃) D2 | None | Inr x₂ with natEQ x x'
  lem-subst (TAVar x₄) D2 | None | Inr x₃ | Inl x₂ = abort ((flip x₃) x₂)
  lem-subst (TAVar x₄) D2 | None | Inr x₃ | Inr x₂ = abort (somenotnone (! x₄))
  lem-subst (TALam D1) D2 = {!!}
  lem-subst (TAAp D1 D2) D3 = TAAp (lem-subst D1 D3) (lem-subst D2 D3)
  lem-subst (TAEHole x₁ x₂) D2 = TAEHole x₁ {!!}
  lem-subst (TANEHole x₁ D1 x₂) D2 = TANEHole x₁ (lem-subst D1 D2) {!!}
  lem-subst (TACast D1 x₁) D2 = TACast (lem-subst D1 D2) x₁
  lem-subst (TAFailedCast D1 x₁ x₂ x₃) D2 = TAFailedCast (lem-subst D1 D2) x₁ x₂ x₃

  -- todo: rename
  pres-lem3 : ∀{ Δ Γ d τ d' } →
            Δ , Γ ⊢ d :: τ →
            d →> d' →
            Δ , Γ ⊢ d' :: τ
  pres-lem3 TAConst ()
  pres-lem3 (TAVar x₁) ()
  pres-lem3 (TALam ta) ()
  pres-lem3 (TAAp (TALam ta) ta₁) ITLam = lem-subst ta ta₁
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
