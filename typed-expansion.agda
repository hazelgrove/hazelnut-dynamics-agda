open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency
open import lemmas-disjointness

open import structural-assumptions
open import structural

module typed-expansion where
  lem-weakenΔ2 : ∀{Δ1 Δ2 Γ d τ} → Δ1 ## Δ2 → Δ2 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  lem-weakenΔ2 {Δ1} {Δ2} {Γ} {d} {τ} disj D = tr (λ q → q , Γ ⊢ d :: τ) (∪comm Δ2 Δ1 (##-comm disj)) (lem-weakenΔ1 (##-comm disj) D)

  mutual
    typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth ESConst = TAConst
    typed-expansion-synth (ESVar x₁) = TAVar x₁
    typed-expansion-synth (ESLam x₁ ex) = TALam x₁ (typed-expansion-synth ex)
    typed-expansion-synth (ESAp {Δ1 = Δ1} _ d x₁ x₂ x₃ x₄)
      with typed-expansion-ana x₃ | typed-expansion-ana x₄
    ... | con1 , ih1 | con2 , ih2  = TAAp (TACast (lem-weakenΔ1 d ih1) con1) (TACast (lem-weakenΔ2 {Δ1 = Δ1} d ih2) con2)
    typed-expansion-synth (ESEHole {Γ = Γ} {u = u})  = TAEHole (ctx-top ∅ u (Γ , ⦇⦈) refl)(STAId (λ x τ z → z))
    typed-expansion-synth (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} (d1 , d2) ex)
      with typed-expansion-synth ex
    ... | ih1 = TANEHole {Δ = Δ ,, (u , Γ , ⦇⦈)} (ctx-top Δ u (Γ , ⦇⦈) (d2 u (lem-domsingle _ _))) (lem-weakenΔ1 (d1 , d2) ih1)(STAId (λ x τ₁ z → z))
    typed-expansion-synth (ESAsc x)
      with typed-expansion-ana x
    ... | con , ih = TACast ih con

    typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana (EALam x₁ MAHole ex)
      with typed-expansion-ana ex
    ... | con , D = TCHole1 , TALam x₁ D
    typed-expansion-ana (EALam x₁ MAArr ex)
      with typed-expansion-ana ex
    ... | con , D = TCArr TCRefl con , TALam x₁ D
    typed-expansion-ana (EASubsume x x₁ x₂ x₃) = ~sym x₃ , typed-expansion-synth x₂
    typed-expansion-ana (EAEHole {Γ = Γ} {u = u}) = TCRefl , TAEHole (ctx-top ∅ u (Γ , _) refl) (STAId (λ x τ z → z))
    typed-expansion-ana (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ} (d1 , d2) x)
      with typed-expansion-synth x
    ... | ih1 = TCRefl , TANEHole {Δ = Δ ,, (u , Γ , τ)} (ctx-top Δ u (Γ , τ) (d2 u (lem-domsingle _ _)) ) (lem-weakenΔ1 (d1 , d2) ih1) (STAId (λ x₁ τ₁ z → z))
