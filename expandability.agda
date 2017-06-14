open import Nat
open import Prelude
open import List
open import core
open import contexts
open import htype-decidable

module expandability where
  mutual
    expandability-synth : {Γ : tctx} {e : hexp} {τ : htyp} →
                          Γ ⊢ e => τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    expandability-synth SConst = c , ∅ , ESConst
    expandability-synth (SAsc {τ = τ} wt)
      with expandability-ana wt
    ... | d' , Δ' , τ' , D with htype-dec τ τ'
    ... | Inl _ = d' , Δ' , ESAsc2 D
    ... | Inr x = (< _ > d') , Δ' , ESAsc1 D x
    expandability-synth (SVar {n = n} x) = X n , ∅ , ESVar x
    expandability-synth (SAp wt1 MAHole wt2)
      with expandability-synth wt1 | expandability-ana wt2
    ... | d1 , Δ1 , D1
        | d2 , Δ2 , τ2 , D2  = ((< τ2 ==> ⦇⦈ > d1) ∘ d2) , (Δ1 ∪ Δ2) , ESAp1 {!!} wt1 {!!} D2
    expandability-synth (SAp wt1 (MAArr {τ2 = τ2}) wt2)
      with expandability-synth wt1 | expandability-ana wt2
    ... | d1 , Δ1 , D1
        | d2 , Δ2 , τ2' , D2
      with htype-dec τ2 τ2'
    expandability-synth (SAp wt1 MAArr wt2) | d1 , Δ1 , D1 | d2 , Δ2 , τ2' , D2 | Inr neq  = (d1 ∘ (< {!τ2'!} > d2)) , (Δ1 ∪ Δ2) , ESAp2 {Δ1 = Δ1} {Δ2 = Δ2} {!!} {!D1!} {!!} neq
    expandability-synth (SAp wt1 MAArr wt2) | d1 , Δ1 , D1 | d2 , Δ2 , τ2 , D2  | Inl refl = (d1 ∘ d2) , (Δ1 ∪ Δ2) , ESAp3 {Δ1 = Δ1} {Δ2 = Δ2} {!!} {!D1!} {!!}
    expandability-synth SEHole = _ , _ , ESEHole
    expandability-synth (SNEHole wt) with expandability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESNEHole wt'
    expandability-synth (SLam x₁ wt) with expandability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESLam x₁ wt'

    expandability-ana : {Γ : tctx} {e : hexp} {τ : htyp} →
                         Γ ⊢ e <= τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    expandability-ana (ASubsume wt x₁) with expandability-synth wt
    ... | d' , Δ' , D' = d' , Δ' , _ , EASubsume (λ x → {!!}) (λ x → {!!}) D' x₁
    expandability-ana (ALam x₁ MAHole wt) with expandability-ana wt
    ... | d' , Δ' , τ' , D'  = {!!}
    expandability-ana (ALam x₁ MAArr wt) with expandability-ana wt
    ... | d' , Δ' , τ' , D' = _ , _ , _ , EALam x₁ D'
