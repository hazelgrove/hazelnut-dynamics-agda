open import Nat
open import Prelude
open import List
open import core
open import correspondence

module typed-expansion where
  mutual
    typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth ESConst = TAConst
    typed-expansion-synth (ESVar x₁) = TAVar x₁
    typed-expansion-synth (ESLam x₁ ex) = TALam (typed-expansion-synth ex)
    typed-expansion-synth (ESAp1 x x₁ x₂ x₃) = TAAp {!!} MAHole {!!}
    typed-expansion-synth (ESAp2 x ex x₁ x₂) = TAAp {!!} MAArr {!!}
    typed-expansion-synth (ESAp3 x ex x₁)    = TAAp {!!} MAArr {!!}
    typed-expansion-synth ESEHole = TAEHole (λ x d x₁ → ⦇⦈ , {!!} , {!!})
    typed-expansion-synth (ESNEHole ex) = TANEHole (typed-expansion-synth ex) (λ x d x₁ → {!!} , {!!} , {!!})
    typed-expansion-synth (ESAsc1 x x₁)
      with typed-expansion-ana x
    ... | con , ih = TACast ih con
    typed-expansion-synth (ESAsc2 x)
      with typed-expansion-ana x
    ... | con , ih = {!!}

    typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ ~ τ') × (Δ , Γ ⊢ d :: τ')
    typed-expansion-ana (EALam x₁ ex)
      with typed-expansion-ana ex
    ... | con , D = (TCArr TCRefl con) , TALam D
    typed-expansion-ana (EASubsume x x₁ x₂ x₃) = x₃ , typed-expansion-synth x₂
    typed-expansion-ana EAEHole = TCRefl , TAEHole {!!}
    typed-expansion-ana (EANEHole x) = TCRefl , TANEHole (typed-expansion-synth x) {!!}
    typed-expansion-ana (EALamHole x y)
      with typed-expansion-ana y
    ... | _ , ih = TCHole2 , TALam ih
