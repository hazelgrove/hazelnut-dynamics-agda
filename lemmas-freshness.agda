open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

module lemmas-freshness where
  -- if x is fresh in an hexp, it's fresh in its expansion
  mutual
    fresh-elab-synth1 : ∀{x e τ d Γ Θ Δ} →
                         x # Γ →
                         freshh x e →
                         Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         fresh x d
    fresh-elab-synth1 _ FRHConst ESConst = FConst
    fresh-elab-synth1 apt (FRHAsc frsh) (ESAsc wf x₁) = FCast (fresh-elab-ana1 apt frsh x₁)
    fresh-elab-synth1 _ (FRHVar x₂) (ESVar x₃) = FVar x₂
    fresh-elab-synth1 {Γ = Γ} apt (FRHLam2 x₂ frsh) (ESLam apt1 wf exp) = FLam x₂ (fresh-elab-synth1 (apart-extend1 Γ x₂ apt) frsh exp)
    fresh-elab-synth1 apt (FRHTLam x₁) (ESTLam x₂) = FTLam (fresh-elab-synth1 apt x₁ x₂)
    fresh-elab-synth1 apt FRHEHole ESEHole = FHole (EFId apt)
    fresh-elab-synth1 apt (FRHNEHole frsh) (ESNEHole x₁ exp) = FNEHole (EFId apt) (fresh-elab-synth1 apt frsh exp)
    fresh-elab-synth1 apt (FRHAp frsh frsh₁) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) =
                               FAp (FCast (fresh-elab-ana1 apt frsh x₅))
                                   (FCast (fresh-elab-ana1 apt frsh₁ x₆))
    fresh-elab-synth1 apt (FRHTAp x₁) (ESTAp apt2 x₂ wf x₃ eq) = FTAp (FCast (fresh-elab-ana1 apt x₁ x₃))

    fresh-elab-ana1 : ∀{ x e τ d τ' Γ Θ Δ} →
                      x # Γ →
                      freshh x e →
                      Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      fresh x d
    fresh-elab-ana1 {Γ = Γ}  apt (FRHLam1 x₁ frsh) (EALam x₂ x₃ exp) = FLam x₁ (fresh-elab-ana1 (apart-extend1 Γ x₁ apt) frsh exp )
    fresh-elab-ana1 apt (FRHTLam x₁) (EATLam _ x₂) = FTLam (fresh-elab-ana1 apt x₁ x₂)
    fresh-elab-ana1 apt frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-elab-synth1 apt frsh x₃
    fresh-elab-ana1 apt FRHEHole EAEHole = FHole (EFId apt)
    fresh-elab-ana1 apt (FRHNEHole frsh) (EANEHole x₁ x₂) = FNEHole (EFId apt) (fresh-elab-synth1 apt frsh x₂)

  -- if x is fresh in the expansion of an hexp, it's fresh in that hexp
  mutual
    fresh-elab-synth2 : ∀{x e τ d Γ Θ Δ} →
                         fresh x d →
                         Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         freshh x e
    fresh-elab-synth2 FConst ESConst = FRHConst
    fresh-elab-synth2 (FVar x₂) (ESVar x₃) = FRHVar x₂
    fresh-elab-synth2 (FLam x₂ frsh) (ESLam apt x₃ exp) = FRHLam2 x₂ (fresh-elab-synth2 frsh exp)
    fresh-elab-synth2 (FTLam x₁) (ESTLam x₂) = FRHTLam (fresh-elab-synth2 x₁ x₂)
    fresh-elab-synth2 (FHole x₁) ESEHole = FRHEHole
    fresh-elab-synth2 (FNEHole x₁ frsh) (ESNEHole x₂ exp) = FRHNEHole (fresh-elab-synth2 frsh exp)
    fresh-elab-synth2 (FAp (FCast frsh) (FCast frsh₁)) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) =
                        FRHAp (fresh-elab-ana2 frsh x₅)
                              (fresh-elab-ana2 frsh₁ x₆)
    fresh-elab-synth2 (FTAp (FCast frsh)) (ESTAp apt x₂ wf x₃ eq) = FRHTAp (fresh-elab-ana2 frsh x₃)
    fresh-elab-synth2 (FCast frsh) (ESAsc wf x₁) = FRHAsc (fresh-elab-ana2 frsh x₁)

    fresh-elab-ana2 : ∀{ x e τ d τ' Γ Θ Δ} →
                      fresh x d →
                      Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      freshh x e
    fresh-elab-ana2 (FLam x₁ frsh) (EALam x₂ x₃ exp) = FRHLam1 x₁ (fresh-elab-ana2 frsh exp)
    fresh-elab-ana2 (FTLam x) (EATLam x₁ x₂) = FRHTLam (fresh-elab-ana2 x x₂)
    fresh-elab-ana2 frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-elab-synth2 frsh x₃
    fresh-elab-ana2 (FHole x₁) EAEHole = FRHEHole
    fresh-elab-ana2 (FNEHole x₁ frsh) (EANEHole x₂ x₃) = FRHNEHole (fresh-elab-synth2 frsh x₃)
