open import Nat
open import Prelude
open import List
open import core
open import contexts
open import htype-decidable

module expandability where
  -- lemma : ∀ { Γ  e τ} →
  --         Γ ⊢ e => ⦇⦈ →
  --         Γ ⊢ e <= τ ==> ⦇⦈
  -- lemma wt = ASubsume wt TCHole1

  mutual
    expandability-synth : {Γ : tctx} {e : hexp} {τ : htyp} →
                          Γ ⊢ e => τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    expandability-synth SConst = _ , _ , ESConst
    expandability-synth (SAsc {τ = τ} wt)
      with expandability-ana wt
    ... | _ , _ , τ' , D with htype-dec τ τ'
    ... | Inl _ = _ , _ , ESAsc2 D
    ... | Inr x = _ , _ , ESAsc1 D x
    expandability-synth (SVar {n = n} x) = _ , _ , ESVar x
    expandability-synth (SAp wt1 MAHole wt2)
      with expandability-ana wt2
    ... | d2 , Δ2 , τ2 , D2 with expandability-ana (ASubsume wt1 TCHole1)
    ... | d1 , Δ1 , τ1 , D1 =  _ , _ , ESAp1 {!!} wt1 D1 D2
    expandability-synth (SAp wt1 (MAArr {τ2 = τ2}) wt2)
      with expandability-synth wt1 | expandability-ana wt2
    ... | d1 , Δ1 , D1
        | d2 , Δ2 , τ2' , D2
      with htype-dec τ2 τ2'
    expandability-synth (SAp wt1 MAArr wt2) | d1 , Δ1 , D1 | d2 , Δ2 , τ2' , D2 | Inr neq  = _ , _ , ESAp2 {!!} {!D1!} {!!} neq
    expandability-synth (SAp wt1 MAArr wt2) | d1 , Δ1 , D1 | d2 , Δ2 , τ2 , D2  | Inl refl = _ , _ , ESAp3 {!!} {!!} {!!}
    expandability-synth SEHole = _ , _ , ESEHole
    expandability-synth (SNEHole wt)
      with expandability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESNEHole wt'
    expandability-synth (SLam x₁ wt)
      with expandability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESLam x₁ wt'

    expandability-ana : {Γ : tctx} {e : hexp} {τ : htyp} →
                         Γ ⊢ e <= τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    expandability-ana {e = e} (ASubsume D x₁)
      with expandability-synth D
    -- these cases just pass through, but we need to pattern match so we can prove things aren't holes
    expandability-ana {e = c} (ASubsume D x₁)                    | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    expandability-ana {e = e ·: x} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    expandability-ana {e = X x} (ASubsume D x₁)                  | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    expandability-ana {e = ·λ x e} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    expandability-ana {e = ·λ x [ x₁ ] e} (ASubsume D x₂)        | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₂
    expandability-ana {e = e1 ∘ e2} (ASubsume D x₁)              | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    -- the two holes are special-cased
    expandability-ana {e = ⦇⦈[ x ]} (ASubsume _ _ )              | _ , _ , _  = _ , _ , _ , EAEHole
    expandability-ana {e = ⦇ e ⦈[ x ]} (ASubsume (SNEHole wt) _) | _ , _ , _  = _ , _ , _ , EANEHole (π2( π2 (expandability-synth wt)))
    -- the lambda cases
    expandability-ana (ALam x₁ MAHole wt)
      with expandability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EALamHole x₁ D'
    expandability-ana (ALam x₁ MAArr wt)
      with expandability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EALam x₁ D'
