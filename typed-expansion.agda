open import Nat
open import Prelude
open import List
open import core
open import correspondence
open import contexts
open import lemmas-consistency

module typed-expansion where
  lem-idsub : ∀{Δ Γ} → Δ , Γ ⊢ id Γ :s: Γ
  lem-idsub = {!!}

  lem-subweak : ∀{Δ Γ Γ' Δ' σ} → Δ , Γ ⊢ σ :s: Γ' → (Δ ∪ Δ') , Γ ⊢ σ :s: Γ'
  lem-subweak sub x d xd∈σ with sub x d xd∈σ
  ... | τ , some , sub' = τ , some , {!!}

  lem-weakenΔ1 : ∀{Δ1 Δ2 Γ d τ} → Δ1 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  lem-weakenΔ1 TAConst = TAConst
  lem-weakenΔ1 (TAVar x₁) = TAVar x₁
  lem-weakenΔ1 (TALam D) = TALam (lem-weakenΔ1 D)
  lem-weakenΔ1 (TAAp D D₁) = TAAp (lem-weakenΔ1 D) (lem-weakenΔ1 D₁)
  lem-weakenΔ1 (TAEHole {Δ = Δ} x y) = TAEHole (x∈∪1 Δ _ _ _ x) (lem-subweak y)
  lem-weakenΔ1 (TANEHole {Δ = Δ} D x y) = TANEHole (x∈∪1 Δ _ _ _ D) (lem-weakenΔ1 x) (lem-subweak y)
  lem-weakenΔ1 (TACast D x) = TACast (lem-weakenΔ1 D) x

  lem-weakenΔ2 : ∀{Δ1 Δ2 Γ d τ} → Δ2 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  lem-weakenΔ2 {Δ1} {Δ2} {Γ} {d} {τ} D = tr (λ q → q , Γ ⊢ d :: τ) (∪comm Δ2 Δ1) (lem-weakenΔ1 D)


  mutual
    typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth ESConst = TAConst
    typed-expansion-synth (ESVar x₁) = TAVar x₁
    typed-expansion-synth (ESLam x₁ ex) = TALam (typed-expansion-synth ex)
    typed-expansion-synth (ESAp {Δ1 = Δ1} x₁ x₂ x₃ x₄)
      with typed-expansion-ana x₃ | typed-expansion-ana x₄
    ... | con1 , ih1 | con2 , ih2  = TAAp (TACast (lem-weakenΔ1 ih1) (~sym con1)) (TACast (lem-weakenΔ2 {Δ1 = Δ1 }ih2) (~sym con2)) --todo: is there a notational inconsistency that means we need this ~sym here, or is it actually important?
    typed-expansion-synth (ESEHole {Γ = Γ} {u = u})  = TAEHole (x∈sing ∅ u (Γ , ⦇⦈)) lem-idsub
    typed-expansion-synth (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} ex)
      with typed-expansion-synth ex
    ... | ih1 = TANEHole {Δ = Δ ,, (u , Γ , ⦇⦈)} (x∈sing Δ u (Γ , ⦇⦈)) (lem-weakenΔ1 ih1) lem-idsub
    typed-expansion-synth (ESAsc x)
      with typed-expansion-ana x
    ... | con , ih = TACast ih (~sym con) --todo: ditto above

    typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ ~ τ') × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana (EALam x₁ ex)
      with typed-expansion-ana ex
    ... | con , D = (TCArr TCRefl con) , TALam D
    typed-expansion-ana (EASubsume x x₁ x₂ x₃) = x₃ , typed-expansion-synth x₂
    typed-expansion-ana (EAEHole {Γ = Γ} {u = u}) = TCRefl , TAEHole (x∈sing ∅ u (Γ , _)) lem-idsub
    typed-expansion-ana (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ}  x)
      with typed-expansion-synth x
    ... | ih1 = TCRefl , TANEHole {Δ = Δ ,, (u , Γ , τ)} (x∈sing Δ u (Γ , τ)) (lem-weakenΔ1 ih1) lem-idsub
    typed-expansion-ana (EALamHole x y)
      with typed-expansion-ana y
    ... | _ , ih = TCHole2 , TALam ih
