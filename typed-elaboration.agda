open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-consistency
open import lemmas-disjointness
open import weakening

module typed-elaboration where
  mutual
    typed-elaboration-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : ihexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-elaboration-synth ESConst = TAConst
    typed-elaboration-synth (ESVar x₁) = TAVar x₁
    typed-elaboration-synth (ESLam x₁ ex) = TALam x₁ (typed-elaboration-synth ex)
    typed-elaboration-synth (ESAp {Δ1 = Δ1} _ d x₁ x₂ x₃ x₄)
      with typed-elaboration-ana x₃ | typed-elaboration-ana x₄
    ... | con1 , ih1 | con2 , ih2  = TAAp (TACast (weaken-ta-Δ1 d ih1) con1) (TACast (weaken-ta-Δ2 {Δ1 = Δ1} d ih2) con2)
    typed-elaboration-synth (ESEHole {Γ = Γ} {u = u})  = TAEHole (ctx-top ∅ u (Γ , ⦇⦈) refl)(STAId (λ x τ z → z))
    typed-elaboration-synth (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} (d1 , d2) ex)
      with typed-elaboration-synth ex
    ... | ih1 = TANEHole {Δ = Δ ,, (u , Γ , ⦇⦈)} (ctx-top Δ u (Γ , ⦇⦈) (d2 u (lem-domsingle _ _))) (weaken-ta-Δ1 (d1 , d2) ih1)(STAId (λ x τ₁ z → z))
    typed-elaboration-synth (ESAsc x)
      with typed-elaboration-ana x
    ... | con , ih = TACast ih con

    typed-elaboration-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : ihexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Γ ⊢ d :: τ')
    typed-elaboration-ana (EALam x₁ MAHole ex)
      with typed-elaboration-ana ex
    ... | con , D = TCHole1 , TALam x₁ D
    typed-elaboration-ana (EALam x₁ MAArr ex)
      with typed-elaboration-ana ex
    ... | con , D = TCArr TCRefl con , TALam x₁ D
    typed-elaboration-ana (EASubsume x x₁ x₂ x₃) = ~sym x₃ , typed-elaboration-synth x₂
    typed-elaboration-ana (EAEHole {Γ = Γ} {u = u}) = TCRefl , TAEHole (ctx-top ∅ u (Γ , _) refl) (STAId (λ x τ z → z))
    typed-elaboration-ana (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ} (d1 , d2) x)
      with typed-elaboration-synth x
    ... | ih1 = TCRefl , TANEHole {Δ = Δ ,, (u , Γ , τ)} (ctx-top Δ u (Γ , τ) (d2 u (lem-domsingle _ _)) ) (weaken-ta-Δ1 (d1 , d2) ih1) (STAId (λ x₁ τ₁ z → z))
