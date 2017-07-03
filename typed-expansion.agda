open import Nat
open import Prelude
open import List
open import core
open import correspondence
open import contexts

module typed-expansion where
  lem-idsub : ∀{Δ Γ} → Δ , Γ ⊢ id Γ :s: Γ
  lem-idsub {Γ = Γ} x d xin with Γ x
  lem-idsub x .(X x) refl | Some τ = τ , refl , TAVar {!!} -- this hole should be refl from pattern matching but it isn't
  lem-idsub x d xin       | None   = abort (somenotnone (! xin))

  mutual
    typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-expansion-synth ESConst = TAConst
    typed-expansion-synth (ESVar x₁) = TAVar x₁
    typed-expansion-synth (ESLam x₁ ex) = TALam (typed-expansion-synth ex)
    -- need a lemma for these two cases that says that if ## and d1 works,
    -- then the union works. it'll use funext
    typed-expansion-synth (ESAp1 x x₁ x₂ x₃)
      with typed-expansion-ana x₂ | typed-expansion-ana x₃
    ... | con1 , ih1 | con2 , ih2 = TAAp {!!} MAHole {!!}
    typed-expansion-synth (ESAp2 x ex x₁ x₂)
      with typed-expansion-synth ex | typed-expansion-ana x₁
    ... | ih1 | con2 , ih2 = TAAp {!!} MAArr {!!}
    typed-expansion-synth (ESAp3 x ex x₁)
      with typed-expansion-synth ex | typed-expansion-ana x₁
    ... | ih1 | con2 , ih2 = TAAp {!ih1!} MAArr {!!}
    typed-expansion-synth ESEHole = TAEHole lem-idsub
    typed-expansion-synth (ESNEHole ex) = TANEHole (typed-expansion-synth ex) lem-idsub
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
    typed-expansion-ana EAEHole = TCRefl , TAEHole lem-idsub
    typed-expansion-ana (EANEHole x) = TCRefl , TANEHole (typed-expansion-synth x) lem-idsub
    typed-expansion-ana (EALamHole x y)
      with typed-expansion-ana y
    ... | _ , ih = TCHole2 , TALam ih
