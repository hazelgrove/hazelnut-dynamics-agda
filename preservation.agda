open import Nat
open import Prelude
open import core
open alpha
open import contexts

open import lemmas-consistency
open import type-assignment-unicity
open import binders-disjoint-checks

open import lemmas-subst-ta
open import lemmas-tysubst-ta
open import lemmas-well-formed

open import rewrite-util

module preservation where

  -- if d and d' both result from filling the hole in ε with terms of the
  -- same type, they too have the same type.
  wt-different-fill : ∀{ Δ Γ Θ d ε d1 d2 d' τ τ1 τ2} →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ , Θ ⊢ d :: τ →
            Δ , Γ , Θ ⊢ d1 :: τ1 →
            Δ , Γ , Θ ⊢ d2 :: τ2 →
            τ1 =α τ2 →
            d' == ε ⟦ d2 ⟧ →
            Σ[ τ' ∈ htyp ] (τ' =α τ × Δ , Γ , Θ ⊢ d' :: τ')
  wt-different-fill {τ2 = τ2} FHOuter D1 D2 D3 A FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = τ2 , alpha-sym A , D3
  wt-different-fill (FHAp1 eps) (TAAp D1 D2 A1) D3 D4 A (FHAp1 D5) with wt-different-fill eps D1 D3 D4 {!   !} D5
  ... | τ1r ==> τ2r , AlphaArr arl arr , p = {!   !} , {!   !} , (TAAp p D2 {!   !}) -- TAAp (wt-different-fill eps D1 D3 D4 {!   !} D5) D2
  wt-different-fill (FHAp2 eps) (TAAp D1 D2 A1) D3 D4 A (FHAp2 D5) = {!   !} -- TAAp D1 (wt-different-fill eps D2 D3 D4 {!   !} D5)
  wt-different-fill (FHTAp eps) (TATAp wf D1 eq) D2 D3 A (FHTAp D4) = {!   !} , {!   !} -- TATAp wf (wt-different-fill eps D1 D2 D3 {!   !} D4) eq
  wt-different-fill (FHNEHole eps) (TANEHole x D1 x₁ eq eq') D2 D3 A (FHNEHole D4) = {!   !} -- TANEHole x (wt-different-fill eps D1 D2 D3 {!   !} D4) x₁ eq eq'
  wt-different-fill (FHCast eps) (TACast D1 wf x A1) D2 D3 A (FHCast D4) = {!   !} -- TACast (wt-different-fill eps D1 D2 D3 {!   !} D4) wf x
  wt-different-fill (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 A (FHFailedCast eps) = {!   !} -- TAFailedCast (wt-different-fill x y D3 D4 {!   !} eps) x₁ x₂ x₃

  -- if a well typed term results from filling the hole in ε, then the term
  -- that filled the hole is also well typed
  wt-filling : ∀{ ε Δ Γ Θ d τ d' } →
             Δ , Γ , Θ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ htyp ] (Δ , Γ , Θ ⊢ d' :: τ')
  wt-filling TAConst FHOuter = _ , TAConst
  wt-filling (TAVar x₁) FHOuter = _ , TAVar x₁
  wt-filling (TALam f wf ta) FHOuter = _ , TALam f wf ta
  wt-filling (TATLam apt ta) FHOuter = _ , TATLam apt ta

  wt-filling (TAAp ta ta₁ alpha) FHOuter = _ , TAAp ta ta₁ alpha
  wt-filling (TAAp ta ta₁ alpha) (FHAp1 eps) = wt-filling ta eps
  wt-filling (TAAp ta ta₁ alpha) (FHAp2 eps) = wt-filling ta₁ eps

  wt-filling (TATAp wf ta eq) FHOuter = _ , TATAp wf ta eq
  wt-filling (TATAp wf ta eq) (FHTAp eps) = wt-filling ta eps

  wt-filling (TAEHole x x₁ eq eq') FHOuter = _ , TAEHole x x₁ eq eq'
  wt-filling (TANEHole x ta x₁ eq eq') FHOuter = _ , TANEHole x ta x₁ eq eq'
  wt-filling (TANEHole x ta x₁ eq eq') (FHNEHole eps) = wt-filling ta eps
  wt-filling (TACast ta wf x alpha) FHOuter = _ , TACast ta wf x alpha
  wt-filling (TACast ta wf x alpha) (FHCast eps) = wt-filling ta eps
  wt-filling (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  wt-filling (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = wt-filling x y

  alpha-refl-ta : ∀{ Δ Γ d τ } → Δ , ∅ , Γ ⊢ d :: τ → Σ[ τ' ∈ htyp ] (τ' =α τ × Δ , ∅ , Γ ⊢ d :: τ')
  alpha-refl-ta {τ = τ} ta = τ , alpha-refl τ , ta

  -- instruction transitions preserve type
  preserve-trans : ∀{ Δ Γ d τ d' } →
            binders-unique d →
            tbinders-unique d →
            tbinders-disjoint-Δ Δ d →
            tbinders-disjoint-Γ Γ d →
            ∅ ⊢ Γ tctxwf →
            Δ hctxwf →
            Δ , ∅ , Γ ⊢ d :: τ →
            d →> d' →
            Σ[ τ' ∈ htyp ] (τ' =α τ × Δ , ∅ , Γ ⊢ d' :: τ')
  preserve-trans _ _ _ _ _ _ TAConst ()
  preserve-trans _ _ _ _ _ _ (TAVar x₁) ()
  preserve-trans _ _ _ _ _ _ (TALam _ _ ta) ()
  preserve-trans {τ = τ} (BUAp (BULam bd x₁) bd₁ (BDLam x₂ x₃)) _ _ _ _ _ (TAAp (TALam apt wf ta) ta₁ alpha) ITLam = alpha-refl-ta (lem-subst apt x₂ bd₁ ta {!   !})
  preserve-trans _ _ _ _ _ _ (TATLam apt ta) ()
  preserve-trans {τ = τ} _ _ _ _ tcwf hcwf (TAAp (TACast ta (WFArr wf1 wf2) (ConsistArr x x₁) alpha) ta₁ alpha') ITApCast with wf-ta tcwf hcwf ta
  ... | WFArr wf1' _ = alpha-refl-ta (TACast (TAAp ta (TACast {!   !} {!   !} (~sym x) {!   !}) {!   !}) wf2 x₁ {!   !})
  preserve-trans {Γ = Γ} {d = ·Λ t d < τ >} {τ = τf} _ (TBUTAp (TBUTLam tbu x₁) _ (TBDTTLam tbd x₂)) (TBDΔTAp (TBDΔTLam tbdd x₆) x₅) (TBDΓTAp (TBDΓTLam tbdg x₄) x₃) tcwf hcwf (TATAp wf (TATLam apt x) eq) ITTLam = alpha-refl-ta (rewrite-typ eq (rewrite-gamma (tctx-sub-closed {Γ} {t} {τ} tcwf)
    (lemma-tysubst wf x₆ x₄ x₁ tbu x)))
  preserve-trans _ (TBUTAp (TBUCast tbu) x₁ (TBDTCast x₂ x₃ x₄)) _ _ _ _ (TATAp wf (TACast ta (WFForall wf2) x alpha) eq) ITTApCast rewrite ! eq
    = alpha-refl-ta (TACast (TATAp wf {!   !} refl) (wf-sub wf wf2 refl) {!   !} {!   !})
  preserve-trans {τ = τ} _ _ _ _ _ _ (TACast ta wf x alpha) (ITCastID {τ1 = τ1} alphaeq) = {!   !}
  preserve-trans {τ = τ} _ _ _ _ _ _ (TACast (TACast ta _ x alpha) _ x₁ alpha2) (ITCastSucceed {τ1 = τ1} g1 g2 alpha3) = {!   !}
  preserve-trans _ _ _ _ _ _ (TACast ta wf x alpha) (ITGround (MGArr x₁)) = {!   !} -- alpha-refl-ta (TACast (TACast ta (WFArr wf wf) (ConsistArr ConsistHole1 ConsistHole1) ) wf ConsistHole1)
  preserve-trans _ _ _ _ _ _ (TACast ta wf x alpha) (ITGround (MGForall x₁)) = {!   !} -- alpha-refl-ta (TACast (TACast ta (WFForall WFHole) (ConsistForall ConsistHole1)) wf ConsistHole1)
  preserve-trans _ _ _ _ _ _ (TACast ta wf TCHole2 alpha) (ITExpand (MGArr x₁)) = {!   !} -- alpha-refl-ta (TACast (TACast ta (WFArr WFHole WFHole) ConsistHole2) wf (ConsistArr ConsistHole2 ConsistHole2))
  preserve-trans _ _ _ _ _ _ (TACast ta wf TCHole2 alpha) (ITExpand (MGForall x₁)) = {!   !} -- alpha-refl-ta (TACast (TACast ta (WFForall WFHole) ConsistHole2) wf (ConsistForall ConsistHole2))
  preserve-trans _ _ _ _ _ _ (TACast (TACast ta _ x alpha) _ x₁ alpha2) (ITCastFail w y z) = {!   !} -- alpha-refl-ta (TAFailedCast ta w y z)
  preserve-trans _ _ _ _ _ _ (TAFailedCast x y z q) ()

  lem-bd-ε1 : ∀{ d ε d0} → d == ε ⟦ d0 ⟧ → binders-unique d → binders-unique d0
  lem-bd-ε1 FHOuter bd = bd
  lem-bd-ε1 (FHAp1 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHAp2 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHTAp eps) (BUTAp bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHNEHole eps) (BUNEHole bd x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHCast eps) (BUCast bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHFailedCast eps) (BUFailedCast bd) = lem-bd-ε1 eps bd

  -- this is the main preservation theorem, gluing together the above
  preservation : {Δ : hctx} {d d' : ihexp} {τ : htyp} {Γ : tctx} →
             binders-unique d →
             tbinders-unique d ->
             tbinders-disjoint-Δ Δ d →
             tbinders-disjoint-Γ Γ d →
             ∅ ⊢ Γ tctxwf →
             Δ hctxwf →
             Δ , ∅ , Γ ⊢ d :: τ →
             d ↦ d' →
             Σ[ τ' ∈ htyp ] (τ' =α τ × Δ , ∅ , Γ ⊢ d' :: τ')
  preservation {τ = τ} bd tbd tbdd tbdg tcwf hcwf D (Step x x₁ x₂)
    with wt-filling D x
  ... | (_ , wt) = let τ' , alpha , trans = preserve-trans (lem-bd-ε1 x bd) {!   !} {!   !} {!   !} tcwf hcwf wt x₁ in
        {!   !} -- τ , ({! alpha  !} , wt-different-fill x D wt {! trans  !} {!   !} {!   !}) -- τ , {!   !} , wt-different-fill x D wt {!   !} x₂ -- (preserve-trans (lem-bd-ε1 x bd) ? ? tcwf hcwf wt x₁) x₂

  -- note that the exact statement of preservation in the paper, where Γ is
  -- empty indicating that the terms are closed, is an immediate corrolary
  -- of the slightly more general statement above.
  preservation' : {Δ : hctx} {d d' : ihexp} {τ : htyp} →
             binders-unique d →
             tbinders-unique d →
             tbinders-disjoint-Δ Δ d →
             Δ hctxwf →
             Δ , ∅ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Σ[ τ' ∈ htyp ] (τ' =α τ × Δ , ∅ , ∅ ⊢ d' :: τ')
  preservation' bu tbu tbdd hcwf = preservation bu tbu tbdd {!   !} wf-empty-tctx hcwf
          