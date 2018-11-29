open import Nat
open import Prelude
open import core
open import contexts
open import htype-decidable
open import lemmas-matching
open import disjointness

module elaborability where
  mutual
    elaborability-synth : {Γ : tctx} {e : hexp} {τ : htyp} →
                          Γ ⊢ e => τ →
                          Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    elaborability-synth SConst = _ , _ , ESConst
    elaborability-synth (SAsc {τ = τ} wt)
      with elaborability-ana wt
    ... | _ , _ , τ' , D  = _ , _ , ESAsc D
    elaborability-synth (SVar x) = _ , _ , ESVar x
    elaborability-synth (SAp dis wt1 m wt2)
      with elaborability-ana (ASubsume wt1 (match-consist m)) | elaborability-ana wt2
    ... | _ , _ , _ , D1 | _ , _ , _ , D2 = _ , _ , ESAp dis (elab-ana-disjoint dis D1 D2) wt1 m D1 D2
    elaborability-synth SEHole = _ , _ , ESEHole
    elaborability-synth (SNEHole new wt)
      with elaborability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESNEHole (elab-new-disjoint-synth new wt') wt'
    elaborability-synth (SLam x₁ wt)
      with elaborability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESLam x₁ wt'

    elaborability-ana : {Γ : tctx} {e : hexp} {τ : htyp} →
                         Γ ⊢ e <= τ →
                          Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    elaborability-ana {e = e} (ASubsume D x₁)
      with elaborability-synth D
    -- these cases just pass through, but we need to pattern match so we can prove things aren't holes
    elaborability-ana {e = c} (ASubsume D x₁)                    | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = e ·: x} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = X x} (ASubsume D x₁)                  | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = ·λ x e} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = ·λ x [ x₁ ] e} (ASubsume D x₂)        | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₂
    elaborability-ana {e = e1 ∘ e2} (ASubsume D x₁)              | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    -- the two holes are special-cased
    elaborability-ana {e = ⦇⦈[ x ]} (ASubsume _ _ )                   | _ , _ , _  = _ , _ , _ , EAEHole
    elaborability-ana {Γ} {⦇⌜ e ⌟⦈[ x ]} (ASubsume (SNEHole new wt) x₂) | _ , _ , ESNEHole x₁ D' with elaborability-synth wt
    ... | w , y , z =  _ , _ , _ , EANEHole (elab-new-disjoint-synth new z) z
    -- the lambda cases
    elaborability-ana (ALam x₁ m wt)
      with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EALam x₁ m D'
