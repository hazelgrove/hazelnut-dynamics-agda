open import Nat
open import Prelude
open import List
open import core
open import correspondence
open import contexts
open import lemmas-consistency

module typed-expansion where
  lem : (Γ : tctx) (x : Nat) → (((id Γ) x) == Some (X x) × (Σ[ τ ∈ htyp ]((Γ x) == Some τ)))
                             + (((id Γ) x) == None)
  lem Γ x with Γ x
  lem Γ x | Some x₁ = Inl (refl , x₁ , refl)
  lem Γ x | None = Inr refl

  lem-idsub : ∀{Δ Γ} → Δ , Γ ⊢ id Γ :s: Γ
  lem-idsub {Δ} {Γ} x d xin with lem Γ x
  lem-idsub {Δ} {Γ} x d xin | Inl (w , y , z) with (! xin) · w
  lem-idsub x .(X x) xin | Inl (w , y , z) | refl = y , z , TAVar z
  lem-idsub x d xin | Inr x₁ = abort (somenotnone ((! xin) · x₁))

  lem-subweak : ∀{Δ Γ Γ' Δ' σ} → Δ , Γ ⊢ σ :s: Γ' → (Δ ∪ Δ') , Γ ⊢ σ :s: Γ'
  lem-subweak sub x d xd∈σ with sub x d xd∈σ
  ... | τ , some , sub' = τ , some , {!!}

  lem-weakenΔ1 : ∀{Δ1 Δ2 Γ d τ} → Δ1 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  lem-weakenΔ1 TAConst = TAConst
  lem-weakenΔ1 (TAVar x₁) = TAVar x₁
  lem-weakenΔ1 (TALam D) = TALam (lem-weakenΔ1 D)
  lem-weakenΔ1 (TAAp D D₁) = TAAp (lem-weakenΔ1 D) (lem-weakenΔ1 D₁)
  lem-weakenΔ1 (TAEHole {Δ = Δ} x y) = TAEHole (x∈∪l Δ _ _ _ x) (lem-subweak y)
  lem-weakenΔ1 (TANEHole {Δ = Δ} D x y) = TANEHole (x∈∪l Δ _ _ _ D) (lem-weakenΔ1 x) (lem-subweak y)
  lem-weakenΔ1 (TACast D x) = TACast (lem-weakenΔ1 D) x
  lem-weakenΔ1 (TAFailedCast x y z w) = TAFailedCast (lem-weakenΔ1 x) y z w

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
    ... | con1 , ih1 | con2 , ih2  = TAAp (TACast (lem-weakenΔ1 ih1) con1) (TACast (lem-weakenΔ2 {Δ1 = Δ1 }ih2) con2)
    typed-expansion-synth (ESEHole {Γ = Γ} {u = u})  = TAEHole (x∈sing ∅ u (Γ , ⦇⦈)) lem-idsub
    typed-expansion-synth (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} ex)
      with typed-expansion-synth ex
    ... | ih1 = TANEHole {Δ = Δ ,, (u , Γ , ⦇⦈)} (x∈sing Δ u (Γ , ⦇⦈)) (lem-weakenΔ1 ih1) lem-idsub
    typed-expansion-synth (ESAsc x)
      with typed-expansion-ana x
    ... | con , ih = TACast ih con

    typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana (EALam x₁ MAHole ex)
      with typed-expansion-ana ex
    ... | con , D = TCHole1 , TALam D
    typed-expansion-ana (EALam x₁ MAArr ex)
      with typed-expansion-ana ex
    ... | con , D = TCArr TCRefl con , TALam D
    typed-expansion-ana (EASubsume x x₁ x₂ x₃) = ~sym x₃ , typed-expansion-synth x₂
    typed-expansion-ana (EAEHole {Γ = Γ} {u = u}) = TCRefl , TAEHole (x∈sing ∅ u (Γ , _)) lem-idsub
    typed-expansion-ana (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ}  x)
      with typed-expansion-synth x
    ... | ih1 = TCRefl , TANEHole {Δ = Δ ,, (u , Γ , τ)} (x∈sing Δ u (Γ , τ)) (lem-weakenΔ1 ih1) lem-idsub
