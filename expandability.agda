open import Nat
open import Prelude
open import List
open import core
open import contexts
open import htype-decidable
open import lemmas-matching
open import disjointness

module expandability where
  mutual
    expandability-synth : {Γ : tctx} {e : hexp} {τ : htyp} →
                          Γ ⊢ e => τ →
                          Σ[ d ∈ dhexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    expandability-synth SConst = _ , _ , ESConst
    expandability-synth (SAsc {τ = τ} wt)
      with expandability-ana wt
    ... | _ , _ , τ' , D  = _ , _ , ESAsc D
    expandability-synth (SVar {n = n} x) = _ , _ , ESVar x
    expandability-synth (SAp dis wt1 m wt2)
      with expandability-ana (ASubsume wt1 (match-consist m)) | expandability-ana wt2
    ... | _ , _ , _ , D1 | _ , _ , _ , D2 = _ , _ , ESAp dis (expand-ana-disjoint dis D1 D2) wt1 m D1 D2
    expandability-synth SEHole = _ , _ , ESEHole
    expandability-synth (SNEHole new wt)
      with expandability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESNEHole (expand-new-disjoint-synth new wt') wt'
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
    expandability-ana {e = ⦇⦈[ x ]} (ASubsume _ _ )                   | _ , _ , _  = _ , _ , _ , EAEHole
    expandability-ana {Γ} {⦇ e ⦈[ x ]} (ASubsume (SNEHole new wt) x₂) | _ , _ , ESNEHole x₁ D' with expandability-synth wt
    ... | w , y , z =  _ , _ , _ , EANEHole (expand-new-disjoint-synth new z) z
    -- the lambda cases
    expandability-ana (ALam x₁ m wt)
      with expandability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EALam x₁ m D'
