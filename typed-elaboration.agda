open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-consistency
open import lemmas-disjointness
open import weakening

module typed-elaboration where

  merge-tctx-wf : ∀ {Θ Γ x x' τ τ'} → Θ ⊢ Γ tctxwf → Θ ⊢ τ wf → x # Γ → (x' , τ') ∈ (Γ ,, (x , τ)) → Θ ⊢ τ' wf
  merge-tctx-wf {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf apt h with (natEQ x x') 
  merge-tctx-wf {Γ = Γ} {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf apt h | Inl eq rewrite (sym eq) 
    with ctxunicity {Γ = (Γ ,, (x , τ))} {n = x} {t = τ} {t' = τ'} (x∈∪r Γ (■ (x , τ)) x τ (x∈■ x τ) (lem-apart-sing-disj apt)) h 
  ... | eq2 rewrite (sym eq2) = twf
  merge-tctx-wf {Γ = Γ} {τ = τ} (CCtx wfs) twf apt h | Inr n with lem-neq-union-eq {Γ = Γ} {τ = τ} (flip n) h
  ... | map = wfs map

  match-arr-wf : ∀ {Θ τ τ1 τ2} → Θ ⊢ τ wf → τ ▸arr (τ1 ==> τ2) → Θ ⊢ (τ1 ==> τ2) wf
  match-arr-wf wf MAHole = WFArr WFHole WFHole
  match-arr-wf wf MAArr = wf

  match-forall-wf : ∀ {Θ τ τ1} → Θ ⊢ τ wf → τ ▸forall (·∀ τ1) → Θ ⊢ (·∀ τ1) wf
  match-forall-wf wf MFHole = WFForall WFHole 
  match-forall-wf wf MFForall = wf

  mutual

    wf-synth : ∀{Θ Γ e τ} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ , Γ ⊢ e => τ → 
                    Θ ⊢ τ wf 
    wf-synth = {!   !}

    typed-elaboration-synth : ∀{Γ e τ d Δ Θ} →
                            Θ ⊢ Γ tctxwf → 
                            Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Θ , Γ ⊢ d :: τ
    typed-elaboration-synth ctxwf ESConst = TAConst
    typed-elaboration-synth ctxwf (ESVar x₁) = TAVar x₁
    typed-elaboration-synth ctxwf (ESLam apt wf ex) = TALam apt wf (typed-elaboration-synth (CCtx (merge-tctx-wf ctxwf wf apt)) ex)
    typed-elaboration-synth ctxwf (ESTLam ex) = TATLam (typed-elaboration-synth (weaken-tctx-wf ctxwf) ex)
    typed-elaboration-synth ctxwf (ESAp {Δ1 = Δ1} _ d x₁ x₂ x₃ x₄)
      with match-arr-wf (wf-synth ctxwf x₁) x₂
    ... | WFArr wf1 wf2
      with typed-elaboration-ana ctxwf (WFArr wf1 wf2) x₃ | typed-elaboration-ana ctxwf wf1 x₄
    ... | con1 , ih1 | con2 , ih2  = TAAp (TACast (weaken-ta-Δ1 d ih1) (WFArr wf1 wf2) con1) (TACast (weaken-ta-Δ2 {Δ1 = Δ1} d ih2) wf1 con2)
    typed-elaboration-synth ctxwf (ESTAp wf x m ex eq) 
      with match-forall-wf (wf-synth ctxwf x) m
    ... | WFForall wf'
      with typed-elaboration-ana ctxwf (WFForall wf') ex 
    ... | con , ih = TATAp wf (TACast ih (WFForall wf') con) {!   !}
    typed-elaboration-synth ctxwf (ESEHole {Γ = Γ} {u = u})  = TAEHole (ctx-top ∅ u (Γ , ⦇-⦈) refl)(STAId (λ x τ z → z))
    typed-elaboration-synth ctxwf (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} (d1 , d2) ex)
      with typed-elaboration-synth ctxwf ex
    ... | ih1 = TANEHole {Δ = Δ ,, (u , Γ , ⦇-⦈)} (ctx-top Δ u (Γ , ⦇-⦈) (d2 u (lem-domsingle _ _))) (weaken-ta-Δ1 (d1 , d2) ih1)(STAId (λ x τ₁ z → z))
    typed-elaboration-synth ctxwf (ESAsc wf x)
      with typed-elaboration-ana ctxwf wf x
    ... | con , ih = TACast ih wf con

    typed-elaboration-ana : ∀{Γ e τ τ' d Δ Θ} →
                          Θ ⊢ Γ tctxwf → 
                          Θ ⊢ τ wf → 
                          Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Θ , Γ ⊢ d :: τ')
    typed-elaboration-ana ctxwf wf (EALam x₁ MAHole ex)
      with typed-elaboration-ana (CCtx (merge-tctx-wf ctxwf wf x₁)) wf ex
    ... | con , D = TCHole1 , TALam x₁ wf D
    typed-elaboration-ana ctxwf (WFArr wf1 wf2) (EALam x₁ MAArr ex)
      with typed-elaboration-ana (CCtx (merge-tctx-wf ctxwf wf1 x₁)) wf2 ex
    ... | con , D = TCArr ~refl con , TALam x₁ wf1 D
    typed-elaboration-ana ctxwf wf (EASubsume x x₁ x₂ x₃) = ~sym x₃ , typed-elaboration-synth ctxwf x₂
    typed-elaboration-ana ctxwf wf (EAEHole {Γ = Γ} {u = u}) = ~refl , TAEHole (ctx-top ∅ u (Γ , _) refl) (STAId (λ x τ z → z))
    typed-elaboration-ana ctxwf wf (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ} (d1 , d2) x)
      with typed-elaboration-synth ctxwf x
    ... | ih1 = ~refl , TANEHole {Δ = Δ ,, (u , Γ , τ)} (ctx-top Δ u (Γ , τ) (d2 u (lem-domsingle _ _)) ) (weaken-ta-Δ1 (d1 , d2) ih1) (STAId (λ x₁ τ₁ z → z))
