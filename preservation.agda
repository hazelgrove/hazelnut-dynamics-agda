open import Nat
open import Prelude
open import List
open import core
open import contexts

open import type-assignment-unicity

module preservation where
  pres-lem : ∀{ Δ Γ d ε d1 d2 d3 τ τ1 } →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ ⊢ d :: τ →
            Δ , Γ ⊢ d1 :: τ1 →
            Δ , Γ ⊢ d2 :: τ1 →
            d3 == ε ⟦ d2 ⟧ →
            Δ , Γ ⊢ d3 :: τ
  pres-lem (FHFinal x) D1 D2 D3 (FHFinal x₁)
    with type-assignment-unicity D1 D2
  ... | refl = D3
  pres-lem (FHFinal x) D1 D2 D3 FHEHole
    with type-assignment-unicity D1 D2
  ... | refl = D3
  pres-lem (FHFinal x) D1 D2 D3 FHNEHoleEvaled
    with type-assignment-unicity D1 D2
  ... | refl = D3
  pres-lem (FHFinal x) D1 D2 D3 (FHNEHoleFinal x₁)
    with type-assignment-unicity D1 D2
  ... | refl = D3
  pres-lem (FHFinal x) D1 D2 D3 (FHCastFinal x₁)
    with type-assignment-unicity D1 D2
  ... | refl = D3

  pres-lem (FHAp1 x eps1) (TAAp D1 x₁ D2) D3 D4 (FHAp1 x₂ eps2)
    = TAAp D1 x₁ {!pres-lem !} -- (pres-lem {!!} D2 {!!} {!!} eps2)

  pres-lem (FHAp2 eps1) D1 D2 D3 (FHAp2 eps2) = {!!}

  pres-lem FHEHole D1 D2 D3 (FHFinal x) = {!!}
  pres-lem FHEHole D1 D2 D3 FHEHole
    with type-assignment-unicity D1 D2
  ... | refl = D3
  pres-lem FHEHole D1 D2 D3 FHNEHoleEvaled = {!!}
  pres-lem FHEHole D1 D2 D3 (FHNEHoleFinal x) = {!!}
  pres-lem FHEHole D1 D2 D3 (FHCastFinal x) = {!!}

  pres-lem FHNEHoleEvaled D1 D2 D3 (FHFinal x) = {!!}
  pres-lem FHNEHoleEvaled D1 D2 D3 FHEHole = {!!}
  pres-lem FHNEHoleEvaled D1 D2 D3 FHNEHoleEvaled = {!!}
  pres-lem FHNEHoleEvaled D1 D2 D3 (FHNEHoleFinal x) = {!!}
  pres-lem FHNEHoleEvaled D1 D2 D3 (FHCastFinal x) = {!!}

  pres-lem (FHNEHoleInside eps1) D1 D2 D3 (FHNEHoleInside eps2) = {!!}

  pres-lem (FHNEHoleFinal x) D1 D2 D3 (FHFinal x₁) = {!!}
  pres-lem (FHNEHoleFinal x) D1 D2 D3 FHEHole = {!!}
  pres-lem (FHNEHoleFinal x) D1 D2 D3 FHNEHoleEvaled = {!!}
  pres-lem (FHNEHoleFinal x) D1 D2 D3 (FHNEHoleFinal x₁) = {!!}
  pres-lem (FHNEHoleFinal x) D1 D2 D3 (FHCastFinal x₁) = {!!}

  pres-lem (FHCast eps1) D1 D2 D3 (FHCast eps2) = {!!}

  pres-lem (FHCastFinal x) D1 D2 D3 (FHFinal x₁) = {!!}
  pres-lem (FHCastFinal x) D1 D2 D3 FHEHole = {!!}
  pres-lem (FHCastFinal x) D1 D2 D3 FHNEHoleEvaled = {!!}
  pres-lem (FHCastFinal x) D1 D2 D3 (FHNEHoleFinal x₁) = {!!}
  pres-lem (FHCastFinal x) D1 D2 D3 (FHCastFinal x₁) = {!!}

  pres-lem2 : ∀{ ε Δ Γ d τ d' } →
             Δ , Γ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ htyp ] (Δ , Γ ⊢ d' :: τ')
  pres-lem2 TAConst (FHFinal x) = b , TAConst
  pres-lem2 (TAVar x₁) (FHFinal x₂) = _ , TAVar x₁
  pres-lem2 (TALam wt) (FHFinal x₁) = _ , TALam wt
  pres-lem2 (TAAp wt x wt₁) (FHFinal x₁) = _ , TAAp wt x wt₁
  pres-lem2 (TAAp wt x wt₁) (FHAp1 x₁ eps) = pres-lem2 wt₁ eps
  pres-lem2 (TAAp wt x wt₁) (FHAp2 eps) = pres-lem2  wt eps
  pres-lem2 (TAEHole x x₁) (FHFinal x₂) = _ , TAEHole x x₁
  pres-lem2 (TAEHole x x₁) FHEHole = _ , TAEHole x x₁
  pres-lem2 (TANEHole x wt x₁) (FHFinal x₂) = _ , TANEHole x wt x₁
  pres-lem2 (TANEHole x wt x₁) FHNEHoleEvaled = _ , TANEHole x wt x₁
  pres-lem2 (TANEHole x wt x₁) (FHNEHoleInside eps) = pres-lem2 wt eps
  pres-lem2 (TANEHole x wt x₁) (FHNEHoleFinal x₂) = _ , TANEHole x wt x₁
  pres-lem2 (TACast wt x) (FHFinal x₁) = _ , TACast wt x
  pres-lem2 (TACast wt x) (FHCast eps) = pres-lem2 wt eps
  pres-lem2 (TACast wt x) (FHCastFinal x₁) = _ , TACast wt x

  pres-lem3 : ∀{ Δ Γ d τ d' } →
            Δ , Γ ⊢ d :: τ →
            Δ ⊢ d →> d' →
            Δ , Γ ⊢ d' :: τ
  pres-lem3 TAConst ()
  pres-lem3 (TAVar x₁) ()
  pres-lem3 (TALam wt) ()
  pres-lem3 (TAAp wt MAHole wt₁) (ITLam x₂) = {!!}
  pres-lem3 (TAAp wt MAArr wt₁) (ITLam x₂) = {!!}
  pres-lem3 (TAEHole x x₁) ITEHole = TAEHole x x₁
  pres-lem3 (TANEHole x wt x₁) (ITNEHole x₂) = TANEHole x wt x₁
  pres-lem3 (TACast wt x) (ITCast x₁ x₂ x₃) = {!!}

  preservation : {Δ : hctx} {d d' : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             Δ ⊢ d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  preservation D (Step x x₁ x₂)
    with pres-lem2 D x
  ... | (_ , wt) = pres-lem x D wt (pres-lem3 wt x₁) x₂

  -- -- constant cases: constants are values and do not step
  -- preservation TAConst (Step () (ITLam x₂) x₃)
  -- preservation TAConst (Step () (ITCast x₁ x₂ x₃) x₄)
  -- preservation TAConst (Step () ITEHole x₂)
  -- preservation TAConst (Step () (ITNEHole x₁) x₂)

  -- -- var case: vars do not step
  -- preservation (TAVar x₁) _ = abort (somenotnone (! x₁))

  -- -- lambda cases: lambdas are values and do not step
  -- preservation (TALam D) (Step () (ITLam x₃) x₄)
  -- preservation (TALam D) (Step () (ITCast x₂ x₃ x₄) x₅)
  -- preservation (TALam D) (Step () ITEHole x₃)
  -- preservation (TALam D) (Step () (ITNEHole x₂) x₃)

  -- -- ap cases
  -- preservation (TAAp D x₁ D₁) (Step x₂ (ITLam x₃) x₄) = {!!}
  -- preservation (TAAp D x D₁) (Step x₁ (ITCast x₂ x₃ x₄) x₅) = {!!}
  -- preservation (TAAp D x D₁) (Step x₁ ITEHole x₃) = {!!}
  -- preservation (TAAp D x D₁) (Step x₁ (ITNEHole x₂) x₃) = {!!}

  -- -- hole cases
  -- preservation (TAEHole x₁ x₂) (Step () (ITLam x₄) x₅)
  -- preservation (TAEHole x x₁) (Step () (ITCast x₃ x₄ x₅) x₆)
  -- preservation (TAEHole x x₁) (Step FHEHole ITEHole FHEHole) = TAEHole x x₁
  -- preservation (TAEHole x x₁) (Step () (ITNEHole x₃) x₄)
  -- preservation (TAEHole x x₁) (Step x₂ x₃ x₄) = {!!}

  -- -- non-empty hole cases
  -- preservation (TANEHole x₁ D x₂) (Step (FHNEHoleInside x₃) (ITLam x₄) (FHNEHoleInside x₅)) = {!!}
  -- preservation (TANEHole x D x₁) (Step (FHNEHoleInside x₂) (ITCast x₃ x₄ x₅) (FHNEHoleInside x₆)) = {!!}
  -- preservation (TANEHole x D x₁) (Step (FHNEHoleInside x₂) ITEHole (FHNEHoleInside x₄)) = {!!}
  -- preservation (TANEHole x D x₁) (Step (FHNEHoleInside x₂) (ITNEHole x₃) (FHNEHoleInside x₄)) = {!!}
  -- preservation (TANEHole x D x₁) (Step (FHNEHoleFinal x₂) (ITNEHole x₃) FHNEHoleEvaled) = TANEHole x D x₁
  -- preservation (TANEHole x x₁ x₂) (Step x₃ x₄ x₅) = {!!}

  -- -- cast cases
  -- preservation (TACast D x₁) (Step (FHCast x₂) (ITLam x₃) x₄) = {!!}
  -- preservation (TACast D x) (Step (FHCast x₁) (ITCast x₂ x₃ x₄) x₅) = {!!}
  -- preservation (TACast D x) (Step (FHCast x₁) ITEHole x₃) = {!!}
  -- preservation (TACast D x) (Step (FHCast x₁) (ITNEHole x₂) x₃) = {!!}
  -- preservation (TACast x x₁) (Step x₂ x₃ x₄) = {!!}
