open import Nat
open import Prelude
open import core
open import contexts

open import lemmas-consistency
open import type-assignment-unicity
open import binders-disjoint-checks

open import lemmas-subst-ta

module preservation where
  open typctx

  -- if d and d' both result from filling the hole in ε with terms of the
  -- same type, they too have the same type.
  wt-different-fill : ∀{ Δ Γ Θ d ε d1 d2 d' τ τ1 } →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ , Θ ⊢ d :: τ →
            Δ , Γ , Θ ⊢ d1 :: τ1 →
            Δ , Γ , Θ ⊢ d2 :: τ1 →
            d' == ε ⟦ d2 ⟧ →
            Δ , Γ , Θ ⊢ d' :: τ
  wt-different-fill FHOuter D1 D2 D3 FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = D3
  wt-different-fill (FHAp1 eps) (TAAp D1 D2) D3 D4 (FHAp1 D5) = TAAp (wt-different-fill eps D1 D3 D4 D5) D2
  wt-different-fill (FHAp2 eps) (TAAp D1 D2) D3 D4 (FHAp2 D5) = TAAp D1 (wt-different-fill eps D2 D3 D4 D5)
  wt-different-fill (FHTAp eps) (TATAp D1) D2 D3 (FHTAp D4) = TATAp (wt-different-fill eps D1 D2 D3 D4)
  wt-different-fill (FHNEHole eps) (TANEHole x D1 x₁) D2 D3 (FHNEHole D4) = TANEHole x (wt-different-fill eps D1 D2 D3 D4) x₁
  wt-different-fill (FHCast eps) (TACast D1 x) D2 D3 (FHCast D4) = TACast (wt-different-fill eps D1 D2 D3 D4) x
  wt-different-fill (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 (FHFailedCast eps) = TAFailedCast (wt-different-fill x y D3 D4 eps) x₁ x₂ x₃

  -- if a well typed term results from filling the hole in ε, then the term
  -- that filled the hole is also well typed
  wt-filling : ∀{ ε Δ Γ Θ d τ d' } →
             Δ , Γ , Θ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ htyp ] (Δ , Γ , Θ ⊢ d' :: τ')
  wt-filling TAConst FHOuter = _ , TAConst
  wt-filling (TAVar x₁) FHOuter = _ , TAVar x₁
  wt-filling (TALam f ta) FHOuter = _ , TALam f ta
  wt-filling (TATLam ta) FHOuter = _ , TATLam ta

  wt-filling (TAAp ta ta₁) FHOuter = _ , TAAp ta ta₁
  wt-filling (TAAp ta ta₁) (FHAp1 eps) = wt-filling ta eps
  wt-filling (TAAp ta ta₁) (FHAp2 eps) = wt-filling ta₁ eps

  wt-filling (TATAp ta) FHOuter = _ , TATAp ta
  wt-filling (TATAp ta) (FHTAp eps) = wt-filling ta eps

  wt-filling (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  wt-filling (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  wt-filling (TANEHole x ta x₁) (FHNEHole eps) = wt-filling ta eps
  wt-filling (TACast ta x) FHOuter = _ , TACast ta x
  wt-filling (TACast ta x) (FHCast eps) = wt-filling ta eps
  wt-filling (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  wt-filling (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = wt-filling x y

  lemma-tysubst : ∀{ Δ Γ Θ d τ t n } -> no-free-tvars Γ -> Δ , Γ , [ Θ newtyp] ⊢ d :: τ -> Δ , Γ , Θ ⊢ (TTyp[ t / n ] d) :: Typ[ t / n ] τ
  lemma-tysubst _ TAConst = TAConst
  lemma-tysubst nfv (TAVar x) = TAVar (nfv x)
  lemma-tysubst (TALam x y) = TALam (lemma-tysubst x) (lemma-tysubst y)
  lemma-tysubst (TATLam x) = {!!}
  lemma-tysubst (TAAp x) = {!!}
  lemma-tysubst (TAEHole x x₁) = {!!}
  lemma-tysubst (TANEHole x x₁ x₂) = {!!}
  lemma-tysubst (TACast x x₁) = {!!}
  lemma-tysubst (TAFailedCast x x₁ x₂ x₃) = {!!}

  -- instruction transitions preserve type
  preserve-trans : ∀{ Δ Γ Θ d τ d' } →
            binders-unique d →
            no-free-tvars Γ →
            Δ , Γ , Θ ⊢ d :: τ →
            d →> d' →
            Δ , Γ , Θ ⊢ d' :: τ
  preserve-trans bd nfv TAConst ()
  preserve-trans bd nfv (TAVar x₁) ()
  preserve-trans bd nfv (TALam _ ta) ()
  preserve-trans (BUAp (BULam bd x₁) bd₁ (BDLam x₂ x₃)) nfv (TAAp (TALam apt ta) ta₁) ITLam = lem-subst apt x₂ bd₁ ta ta₁
  preserve-trans bd nfv (TATLam ta) ()
  -- preserve-trans bd (TAAp (TACast ta TCBase) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ ~refl)) ~refl
  preserve-trans bd nfv (TAAp (TACast ta (TCArr x x₁)) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ (~sym x))) x₁
  preserve-trans bd nfv (TATAp (TACast ta (TCForall x))) ITTApCast = TACast (TATAp ta) (~Typ[] x)
  preserve-trans bd nfv (TATAp (TATLam x)) ITTLam = lemma-tysubst nfv x
  preserve-trans bd nfv (TAEHole x x₁) ()
  preserve-trans bd nfv (TANEHole x ta x₁) ()
  preserve-trans bd nfv (TACast ta x) (ITCastID) = ta
  preserve-trans bd nfv (TACast (TACast ta x) x₁) (ITCastSucceed x₂) = ta
  preserve-trans bd nfv (TACast ta x) (ITGround (MGArr x₁)) = TACast (TACast ta (TCArr TCHole1 TCHole1)) TCHole1
  preserve-trans bd nfv (TACast ta x) (ITGround (MGForall x₁)) = TACast (TACast ta (TCForall TCHole1)) TCHole1
  preserve-trans bd nfv (TACast ta TCHole2) (ITExpand (MGArr x₁)) = TACast (TACast ta TCHole2) (TCArr TCHole2 TCHole2)
  preserve-trans bd nfv (TACast ta TCHole2) (ITExpand (MGForall x₁)) = TACast (TACast ta TCHole2) (TCForall TCHole2)
  preserve-trans bd nfv (TACast (TACast ta x) x₁) (ITCastFail w y z) = TAFailedCast ta w y z
  preserve-trans bd nfv (TAFailedCast x y z q) ()

  lem-bd-ε1 : ∀{ d ε d0} → d == ε ⟦ d0 ⟧ → binders-unique d → binders-unique d0
  lem-bd-ε1 FHOuter bd = bd
  lem-bd-ε1 (FHAp1 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHAp2 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHTAp eps) (BUTAp bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHNEHole eps) (BUNEHole bd x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHCast eps) (BUCast bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHFailedCast eps) (BUFailedCast bd) = lem-bd-ε1 eps bd

  -- this is the main preservation theorem, gluing together the above
  preservation : {Δ : hctx} {d d' : ihexp} {τ : htyp} {Γ : tctx} {Θ : typctx} →
             binders-unique d →
             Δ , Γ , Θ ⊢ d :: τ →
             d ↦ d' →
             Δ , Γ , Θ ⊢ d' :: τ
  preservation bd D (Step x x₁ x₂)
    with wt-filling D x
  ... | (_ , wt) = wt-different-fill x D wt (preserve-trans (lem-bd-ε1 x bd) wt x₁) x₂

  -- note that the exact statement of preservation in the paper, where Γ is
  -- empty indicating that the terms are closed, is an immediate corrolary
  -- of the slightly more general statement above.
  preservation' : {Δ : hctx} {d d' : ihexp} {τ : htyp} →
             binders-unique d →
             Δ , ∅ , ~∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ , ~∅ ⊢ d' :: τ
  preservation' = preservation
