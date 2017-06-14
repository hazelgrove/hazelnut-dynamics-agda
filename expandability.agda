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
    ... | d' , Δ' , τ' , D with htype-dec {!!} τ'
    expandability-synth (SAsc x₁) | d' , Δ' , _ , D | Inl refl = d' , Δ' , ESAsc2 D
    expandability-synth (SAsc x₁) | d' , Δ' , τ' , D | Inr x = (< {!!} > d') , Δ' , ESAsc1 D {!!}
    expandability-synth (SVar {n = n} x) = X n , ∅ , ESVar x
    expandability-synth (SAp D MAHole x₁)
      with expandability-synth D | expandability-ana x₁
    ... | d1 , Δ1 , D1
        | d2 , Δ2 , τ2 , D2  = ((< τ2 ==> ⦇⦈ > d1) ∘ d2) , (Δ1 ∪ Δ2) , ESAp1 {!!} D D2 {!!}
    expandability-synth (SAp D MAArr x₁) = {!!} , {!!} , {!!}
    expandability-synth SEHole = _ , _ , ESEHole
    expandability-synth (SNEHole wt) with expandability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESNEHole wt'
    expandability-synth (SLam x₁ wt) with expandability-synth wt
    ... | d' , Δ' , wt' = _ , ∅ , ESLam wt'

    expandability-ana : {Γ : tctx} {e : hexp} {τ : htyp} →
                         Γ ⊢ e <= τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    expandability-ana (ASubsume wt x₁) with expandability-synth wt
    ... | d' , Δ' , D' = d' , Δ' , _ , EASubsume (λ x → {!!}) (λ x → {!!}) D' x₁
    expandability-ana (ALam x₁ MAHole wt) with expandability-ana wt
    ... | d' , Δ' , τ' , D'  = {!!} , {!!} , {!!} , {!!}
    expandability-ana (ALam x₁ MAArr wt) with expandability-ana wt
    ... | d' , Δ' , τ' , D' = _ , {!!} , {!!} , EALam {!!}
