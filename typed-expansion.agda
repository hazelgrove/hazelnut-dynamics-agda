open import Nat
open import Prelude
open import List
open import core
open import correspondence
open import contexts

module typed-expansion where
  lem-idsub : ∀{Δ Γ} → Δ , Γ ⊢ id Γ :s: Γ
  lem-idsub {Γ = Γ} x d xin with Γ x
  lem-idsub {Γ = Γ} x .(X x) refl | Some τ = τ , refl , TAVar {!!}
  lem-idsub x d () | None

  lem-weakenΔ1 : ∀{Δ1 Δ2 Γ d τ} → Δ1 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  lem-weakenΔ1 TAConst = TAConst
  lem-weakenΔ1 (TAVar x₁) = TAVar x₁
  lem-weakenΔ1 (TALam D) = TALam (lem-weakenΔ1 D)
  lem-weakenΔ1 (TAAp D x D₁) = TAAp (lem-weakenΔ1 D) x (lem-weakenΔ1 D₁)
  lem-weakenΔ1 (TAEHole {Δ = Δ} x) = {!TAEHole!}
  lem-weakenΔ1 (TANEHole D x) = {!!}
  lem-weakenΔ1 (TACast D x) = TACast (lem-weakenΔ1 D) x

  lem-##eq : {Δ1 Δ2 : hctx} (n : Nat) → Δ1 ## Δ2 → Δ1 n == (Δ1 ∪ Δ2) n
  lem-##eq {Δ1} {Δ2} n apart with Δ1 n
  lem-##eq n apart | Some x = refl
  lem-##eq {Δ1} {Δ2} n apart | None with Δ2 n
  lem-##eq n (π1 , π2) | None | Some x = {!!}
  lem-##eq n apart | None | None = refl

  lem-weakenΔ2 : ∀{Δ1 Δ2 Γ d τ} → Δ2 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  lem-weakenΔ2 {Δ1} {Δ2} {Γ} {d} {τ}  D = tr (λ x → x , Γ ⊢ d :: τ) (funext (λ x → {!!})) D

  mutual
    typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth ESConst = TAConst
    typed-expansion-synth (ESVar x₁) = TAVar x₁
    typed-expansion-synth (ESLam x₁ ex) = TALam (typed-expansion-synth ex)
    typed-expansion-synth (ESAp1 {Δ1 = Δ1} x₁ x₂ x₃)
      with typed-expansion-ana x₂ | typed-expansion-ana x₃
    ... | con1 , ih1 | con2 , ih2 = TAAp (TACast (lem-weakenΔ1 ih1) con1) MAArr (lem-weakenΔ2 {Δ1 = Δ1} ih2)
    typed-expansion-synth (ESAp2 {Δ1 = Δ1} ex x₁ x₂)
      with typed-expansion-synth ex | typed-expansion-ana x₁
    ... | ih1 | con2 , ih2 = TAAp (lem-weakenΔ1 ih1) MAArr (TACast (lem-weakenΔ2 {Δ1 = Δ1} ih2) con2)
    typed-expansion-synth (ESAp3 {Δ1 = Δ1} ex x₁)
      with typed-expansion-synth ex | typed-expansion-ana x₁
    ... | ih1 | con2 , ih2 = TAAp (lem-weakenΔ1 ih1) MAArr (lem-weakenΔ2 {Δ1 = Δ1} ih2)
    typed-expansion-synth ESEHole = TAEHole lem-idsub
    typed-expansion-synth (ESNEHole ex) = TANEHole (typed-expansion-synth ex) lem-idsub
    typed-expansion-synth (ESAsc1 x x₁)
      with typed-expansion-ana x
    ... | con , ih = TACast ih con
    typed-expansion-synth (ESAsc2 x)
      with typed-expansion-ana x
    ... | con , ih = ih

    typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ ~ τ') × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana (EALam x₁ ex)
      with typed-expansion-ana ex
    ... | con , D = (TCArr TCRefl con) , TALam D
    typed-expansion-ana (EASubsume x x₁ x₂ x₃) = x₃ , typed-expansion-synth x₂
    typed-expansion-ana EAEHole = TCRefl , TAEHole lem-idsub
    typed-expansion-ana (EANEHole x) = TCRefl , TANEHole (typed-expansion-synth x) lem-idsub
    typed-expansion-ana (EALamHole x y)
      with typed-expansion-ana y
    ... | _ , ih = TCHole2 , TALam ih
