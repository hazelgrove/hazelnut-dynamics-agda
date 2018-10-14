open import Nat
open import Prelude
open import List
open import core
open import contexts

open import lemmas-consistency
open import type-assignment-unicity
open import binders-disjoint-checks

open import structural-assumptions

module preservation where
  -- if d and d' both result from filling the hole in ε with terms of the
  -- same type, they too have the same type.
  wt-different-fill : ∀{ Δ Γ d ε d1 d2 d' τ τ1 } →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ ⊢ d :: τ →
            Δ , Γ ⊢ d1 :: τ1 →
            Δ , Γ ⊢ d2 :: τ1 →
            d' == ε ⟦ d2 ⟧ →
            Δ , Γ ⊢ d' :: τ
  wt-different-fill FHOuter D1 D2 D3 FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = D3
  wt-different-fill (FHAp1 eps) (TAAp D1 D2) D3 D4 (FHAp1 D5) = TAAp (wt-different-fill eps D1 D3 D4 D5) D2
  wt-different-fill (FHAp2 eps) (TAAp D1 D2) D3 D4 (FHAp2 D5) = TAAp D1 (wt-different-fill eps D2 D3 D4 D5)
  wt-different-fill (FHNEHole eps) (TANEHole x D1 x₁) D2 D3 (FHNEHole D4) = TANEHole x (wt-different-fill eps D1 D2 D3 D4) x₁
  wt-different-fill (FHCast eps) (TACast D1 x) D2 D3 (FHCast D4) = TACast (wt-different-fill eps D1 D2 D3 D4) x
  wt-different-fill (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 (FHFailedCast eps) = TAFailedCast (wt-different-fill x y D3 D4 eps) x₁ x₂ x₃

  -- if a well typed term results from filling the hole in ε, then the term
  -- that filled the hole is also well typed
  wt-filling : ∀{ ε Δ Γ d τ d' } →
             Δ , Γ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ htyp ] (Δ , Γ ⊢ d' :: τ')
  wt-filling TAConst FHOuter = _ , TAConst
  wt-filling (TAVar x₁) FHOuter = _ , TAVar x₁
  wt-filling (TALam f ta) FHOuter = _ , TALam f ta

  wt-filling (TAAp ta ta₁) FHOuter = _ , TAAp ta ta₁
  wt-filling (TAAp ta ta₁) (FHAp1 eps) = wt-filling ta eps
  wt-filling (TAAp ta ta₁) (FHAp2 eps) = wt-filling ta₁ eps

  wt-filling (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  wt-filling (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  wt-filling (TANEHole x ta x₁) (FHNEHole eps) = wt-filling ta eps
  wt-filling (TACast ta x) FHOuter = _ , TACast ta x
  wt-filling (TACast ta x) (FHCast eps) = wt-filling ta eps
  wt-filling (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  wt-filling (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = wt-filling x y

  -- instruction transitions preserve type
  preserve-trans : ∀{ Δ Γ d τ d' } →
            binders-unique d →
            Δ , Γ ⊢ d :: τ →
            d →> d' →
            Δ , Γ ⊢ d' :: τ
  preserve-trans bd TAConst ()
  preserve-trans bd (TAVar x₁) ()
  preserve-trans bd (TALam _ ta) ()
  preserve-trans (BUAp (BULam bd x₁) bd₁ (BDLam x₂ x₃)) (TAAp (TALam apt ta) ta₁) ITLam = lem-subst apt x₂ bd bd₁ ta ta₁
  preserve-trans bd (TAAp (TACast ta TCRefl) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ TCRefl)) TCRefl
  preserve-trans bd (TAAp (TACast ta (TCArr x x₁)) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ (~sym x))) x₁
  preserve-trans bd (TAEHole x x₁) ()
  preserve-trans bd (TANEHole x ta x₁) ()
  preserve-trans bd (TACast ta x) (ITCastID) = ta
  preserve-trans bd (TACast (TACast ta x) x₁) (ITCastSucceed x₂) = ta
  preserve-trans bd (TACast ta x) (ITGround (MGArr x₁)) = TACast (TACast ta (TCArr TCHole1 TCHole1)) TCHole1
  preserve-trans bd (TACast ta TCHole2) (ITExpand (MGArr x₁)) = TACast (TACast ta TCHole2) (TCArr TCHole2 TCHole2)
  preserve-trans bd (TACast (TACast ta x) x₁) (ITCastFail w y z) = TAFailedCast ta w y z
  preserve-trans bd (TAFailedCast x y z q) ()

  -- binder uniqueness is preserved by hole filling
  lem-bd-ε1 : ∀{ d ε d0} → d == ε ⟦ d0 ⟧ → binders-unique d → binders-unique d0
  lem-bd-ε1 FHOuter bd = bd
  lem-bd-ε1 (FHAp1 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHAp2 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHNEHole eps) (BUNEHole bd x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHCast eps) (BUCast bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHFailedCast eps) (BUFailedCast bd) = lem-bd-ε1 eps bd

  lem-bd-ε2 : ∀{ d ε d0} → d == ε ⟦ d0 ⟧ → binders-unique d0 → binders-unique d
  lem-bd-ε2 FHOuter bd = bd
  lem-bd-ε2 (FHAp1 eps) bd = {!!}
  lem-bd-ε2 (FHAp2 eps) bd = {!!}
  lem-bd-ε2 (FHNEHole eps) bd = {!!}
  lem-bd-ε2 (FHCast eps) bd = {!!}
  lem-bd-ε2 (FHFailedCast eps) bd = {!!}

  mutual

    bu-subst : ∀{d1 d2 x} → binders-unique d1 → binders-unique d2 → unbound-in x d1 → binders-unique ([ d2 / x ] d1)
    bu-subst BUHole bu2 ub = BUHole
    bu-subst {x = x} (BUVar {x = y}) bu2 UBVar with natEQ y x
    bu-subst BUVar bu2 UBVar | Inl refl = bu2
    bu-subst BUVar bu2 UBVar | Inr x₂ = BUVar
    bu-subst {x = x} (BULam {x = y}  bu1 x₂) bu2 (UBLam2 x₃ ub) with natEQ y x
    bu-subst (BULam bu1 x₃) bu2 (UBLam2 x₄ ub) | Inl refl = BULam bu1 ub -- can also abort here; odd
    bu-subst (BULam bu1 x₃) bu2 (UBLam2 x₄ ub) | Inr x₂ = BULam (bu-subst bu1 bu2 ub) {!!}
    bu-subst (BUEHole x₁) bu2 (UBHole x₂) = BUEHole {!!}
    bu-subst (BUNEHole bu1 x₁) bu2 (UBNEHole x₂ ub) = BUNEHole (bu-subst bu1 bu2 ub) {!!}
    bu-subst (BUAp bu1 bu2 x₁) bu3 (UBAp ub ub₁) = BUAp (bu-subst bu1 bu3 ub) (bu-subst bu2 bu3 ub₁) {!!}
    bu-subst (BUCast bu1) bu2 (UBCast ub) = BUCast (bu-subst bu1 bu2 ub)
    bu-subst (BUFailedCast bu1) bu2 (UBFailedCast ub) = BUFailedCast (bu-subst bu1 bu2 ub)

  bu-trans : ∀{d0 d0'} → binders-unique d0 → d0 →> d0' → binders-unique d0'
  bu-trans BUHole ()
  bu-trans BUVar ()
  bu-trans (BULam bu x₁) ()
  bu-trans (BUEHole x) ()
  bu-trans (BUNEHole bu x) ()
  bu-trans (BUAp (BULam bu x₁) bu₁ (BDLam x₂ x₃)) ITLam = bu-subst bu bu₁ x₁
  bu-trans (BUAp (BUCast bu) bu₁ (BDCast x)) ITApCast = BUCast (BUAp bu (BUCast bu₁) (lem-bd-into-cast x))
  bu-trans (BUCast bu) ITCastID = bu
  bu-trans (BUCast (BUCast bu)) (ITCastSucceed x) = bu
  bu-trans (BUCast (BUCast bu)) (ITCastFail x x₁ x₂) = BUFailedCast bu
  bu-trans (BUCast bu) (ITGround x) = BUCast (BUCast bu)
  bu-trans (BUCast bu) (ITExpand x) = BUCast (BUCast bu)
  bu-trans (BUFailedCast bu) ()

  -- this is the main preservation theorem, gluing together the above
  preservation : {Δ : hctx} {d d' : ihexp} {τ : htyp} {Γ : tctx} →
             binders-unique d →
             Δ , Γ ⊢ d :: τ →
             d ↦ d' →
             Δ , Γ ⊢ d' :: τ × binders-unique d'
  preservation bd D (Step x x₁ x₂)
    with wt-filling D x
  ... | (_ , wt) = wt-different-fill x D wt (preserve-trans (lem-bd-ε1 x bd) wt x₁) x₂ ,
                   {!(bu-trans (lem-bd-ε1 x bd) x₁)!}
