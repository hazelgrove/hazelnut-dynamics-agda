{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
-- open typctx
open import contexts
open import lemmas-consistency
open import lemmas-disjointness
open import weakening
open import lemmas-well-formed

module typed-elaboration where

  mutual 

    typed-elaboration-synth : ∀{Γ e τ d Δ Θ} →
                            Θ ⊢ Γ tctxwf → 
                            Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Θ , Γ ⊢ d :: τ
    typed-elaboration-synth ctxwf ESConst = TAConst
    typed-elaboration-synth ctxwf (ESVar x₁) = TAVar x₁
    typed-elaboration-synth ctxwf (ESLam apt wf ex) = TALam apt wf (typed-elaboration-synth (merge-tctx-wf ctxwf wf) ex)
    typed-elaboration-synth ctxwf (ESTLam ex) = {! TATLam (typed-elaboration-synth (weaken-tctx-wf ctxwf) ex) !}
    typed-elaboration-synth ctxwf (ESAp {Δ1 = Δ1} _ d x₁ x₂ x₃ x₄)
      with match-arr-wf (wf-synth ctxwf x₁) x₂
    ... | WFArr wf1 wf2
      with typed-elaboration-ana ctxwf (WFArr wf1 wf2) x₃ | typed-elaboration-ana ctxwf wf1 x₄
    ... | con1 , ih1 | con2 , ih2  = {! TAAp (TACast (weaken-ta-Δ1 d ih1) (WFArr wf1 wf2) con1) (TACast (weaken-ta-Δ2 {Δ1 = Δ1} d ih2) wf1 con2) !}
    typed-elaboration-synth ctxwf (ESTAp wf x m ex eq) 
      with match-forall-wf (wf-synth ctxwf x) m
    ... | wf'
      with typed-elaboration-ana ctxwf wf' ex 
    ... | con , ih = TATAp wf {! (TACast ih wf' con) !} eq
    typed-elaboration-synth ctxwf (ESEHole {Γ = Γ} {u = u})  = {! TAEHole (ctx-top ∅ u (Γ , ⦇-⦈) refl) !} {! (STAId (λ x τ z → z)) !}
    typed-elaboration-synth {Θ = Θ} ctxwf (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} (d1 , d2) ex)
      with typed-elaboration-synth ctxwf ex
    ... | ih1 = {! TANEHole {Δ = Δ ,, (u , Θ , Γ , ⦇-⦈)} (ctx-top Δ u (Γ , ⦇-⦈) (d2 u (lem-domsingle _ _))) (weaken-ta-Δ1 (d1 , d2) ih1) !} {! (STAId (λ x τ₁ z → z)) !}
    typed-elaboration-synth ctxwf (ESAsc wf x)
      with typed-elaboration-ana ctxwf wf x
    ... | con , ih = {! TACast ih wf con !}

    typed-elaboration-ana : ∀{Γ e τ τ' d Δ Θ} →
                          Θ ⊢ Γ tctxwf → 
                          Θ ⊢ τ wf → 
                          Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Θ , Γ ⊢ d :: τ')
    typed-elaboration-ana ctxwf wf (EALam x₁ MAHole ex)
      with typed-elaboration-ana (merge-tctx-wf ctxwf wf) wf ex
    ... | con , D = {! TCHole1 !} , TALam x₁ wf D
    typed-elaboration-ana ctxwf (WFArr wf1 wf2) (EALam x₁ MAArr ex)
      with typed-elaboration-ana (merge-tctx-wf ctxwf wf1) wf2 ex
    ... | con , D = {! TCArr ~refl con !} , TALam x₁ wf1 D
    typed-elaboration-ana ctxwf wf (EASubsume x x₁ x₂ x₃) = ~sym x₃ , typed-elaboration-synth ctxwf x₂
    typed-elaboration-ana ctxwf wf (EAEHole {Γ = Γ} {u = u}) = ~refl , {! TAEHole (ctx-top ∅ u (Γ , _) refl) !} {! (STAId (λ x τ z → z)) !}
    typed-elaboration-ana {Θ = Θ} ctxwf wf (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ} (d1 , d2) x)
      with typed-elaboration-synth ctxwf x
    ... | ih1 = ~refl , {! TANEHole {Δ = Δ ,, (u , Θ , Γ , τ)} (ctx-top Δ u (Γ , τ) (d2 u (lem-domsingle _ _)) ) (weaken-ta-Δ1 (d1 , d2) ih1) !} {! (STAId (λ x₁ τ₁ z → z)) !}
    typed-elaboration-ana {e = ·Λ x₂ e} x x₁ (EATLam x₃ x₄ x₅ x₆) = {!   !}
