open import Nat
open import Prelude
open import core
open import contexts
open import htype-decidable
open import lemmas-matching
open import disjointness

module elaborability where
  mutual
    elaborability-synth : ∀{Γ e τ Θ} →
                          Θ , Γ ⊢ e => τ →
                          Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ]
                            (Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    elaborability-synth SConst = _ , _ , ESConst
    elaborability-synth (SAsc {τ = τ} wf wt)
      with elaborability-ana wt
    ... | _ , _ , τ' , D  = _ , _ , ESAsc wf D
    elaborability-synth (SVar x) = _ , _ , ESVar x
    elaborability-synth (SAp dis wt1 m wt2)
      with elaborability-ana (ASubsume wt1 (match-consist m)) | elaborability-ana wt2
    ... | _ , _ , _ , D1 | _ , _ , _ , D2 = _ , _ , ESAp dis (elab-ana-disjoint dis D1 D2) wt1 m D1 D2
    elaborability-synth (STAp wf wt m eq) with elaborability-ana (ASubsume wt (forall-match-consist m))
    ... | _ , _ , _ , wt' = _ , _ , ESTAp wf wt m wt' eq
    elaborability-synth SEHole = _ , _ , ESEHole
    elaborability-synth (SNEHole new wt)
      with elaborability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESNEHole (elab-new-disjoint-synth new wt') wt'
    elaborability-synth (SLam apt wf wt)
      with elaborability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESLam apt wf wt'
    elaborability-synth (STLam wt) with elaborability-synth wt
    ... | _ , _ , wt' = _ , _ , ESTLam wt'

    elaborability-ana : ∀{Γ e τ Θ} →
                         Θ , Γ ⊢ e <= τ →
                          Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    elaborability-ana {e = e} (ASubsume D x₁)
      with elaborability-synth D
    -- these cases just pass through, but we need to pattern match so we can prove things aren't holes
    elaborability-ana {e = c} (ASubsume D x₁)                    | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = e ·: x} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = X x} (ASubsume D x₁)                  | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = ·λ x e} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = ·λ x [ x₁ ] e} (ASubsume D x₂)        | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₂
    elaborability-ana {e = ·Λ _ e} (ASubsume D x₁)                 | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁ 
    elaborability-ana {e = e1 ∘ e2} (ASubsume D x₁)              | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = e < τ >} (ASubsume D x₁)              | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁ 
    -- the two holes are special-cased
    elaborability-ana {e = ⦇-⦈[ x ]} (ASubsume _ _ )                   | _ , _ , _  = _ , _ , _ , EAEHole
    elaborability-ana {Γ} {⦇⌜ e ⌟⦈[ x ]} (ASubsume (SNEHole new wt) x₂) | _ , _ , ESNEHole x₁ D' with elaborability-synth wt
    ... | w , y , z =  _ , _ , _ , EANEHole (elab-new-disjoint-synth new z) z
    -- the lambda cases
    elaborability-ana (ALam x₁ m wt)
      with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EALam x₁ m D'
    elaborability-ana {e = ·Λ _ c} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ (e ·: x)} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ (X x)} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ (·λ x e)} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ (·λ x [ x₁ ] e)} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ (·Λ x e)} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ (e ∘ e₁)} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ (e < x >)} (ATLam m wt) with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EATLam (λ u ()) (λ e' u ()) m D'
    elaborability-ana {e = ·Λ _ ⦇-⦈[ x ]} (ATLam MFHole wt) = _ , _ , _ , EASubsume (λ u ()) (λ e' u ()) (ESTLam ESEHole) TCHole2
    elaborability-ana {e = ·Λ _ ⦇-⦈[ x ]} (ATLam MFForall wt) = _ , _ , _ , EASubsume (λ u ()) (λ e' u ()) (ESTLam ESEHole) (TCForall TCHole1)
    elaborability-ana {e = ·Λ _ ⦇⌜ e ⌟⦈[ x ]} (ATLam m (ASubsume (SNEHole x₁ wt) cons)) with elaborability-synth wt 
    elaborability-ana {_} {·Λ _ ⦇⌜ e ⌟⦈[ x ]} (ATLam MFHole (ASubsume (SNEHole x₁ wt) cons)) | _ , _ , D' = _ , _ , _ , EASubsume (λ u ()) (λ e' u ()) (ESTLam (ESNEHole {!   !} D')) TCHole2
    elaborability-ana {_} {·Λ _ ⦇⌜ e ⌟⦈[ x ]} (ATLam MFForall (ASubsume (SNEHole x₁ wt) cons)) | _ , _ , D' = _ , _ , _ , EASubsume (λ u ()) (λ e' u ()) (ESTLam (ESNEHole {!   !} D')) (TCForall cons)