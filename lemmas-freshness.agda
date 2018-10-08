open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

module lemmas-freshness where
  -- if x is fresh in an hexp, it's fresh in its expansion
  mutual
    fresh-expand-synth1 : ∀{x e τ d Γ Δ} →
                         x # Γ →
                         freshh x e →
                         Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         fresh x d
    fresh-expand-synth1 _ FRHConst ESConst = FConst
    fresh-expand-synth1 apt (FRHAsc frsh) (ESAsc x₁) = FCast (fresh-expand-ana1 apt frsh x₁)
    fresh-expand-synth1 _ (FRHVar x₂) (ESVar x₃) = FVar x₂
    fresh-expand-synth1 {Γ = Γ} apt (FRHLam2 x₂ frsh) (ESLam x₃ exp) = FLam x₂ (fresh-expand-synth1 (apart-extend1 Γ x₂ apt) frsh exp)
    fresh-expand-synth1 apt FRHEHole ESEHole = FHole (EFId apt)
    fresh-expand-synth1 apt (FRHNEHole frsh) (ESNEHole x₁ exp) = FNEHole (EFId apt) (fresh-expand-synth1 apt frsh exp)
    fresh-expand-synth1 apt (FRHAp frsh frsh₁) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) =
                               FAp (FCast (fresh-expand-ana1 apt frsh x₅))
                                   (FCast (fresh-expand-ana1 apt frsh₁ x₆))

    fresh-expand-ana1 : ∀{ x e τ d τ' Γ Δ} →
                      x # Γ →
                      freshh x e →
                      Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      fresh x d
    fresh-expand-ana1 {Γ = Γ}  apt (FRHLam1 x₁ frsh) (EALam x₂ x₃ exp) = FLam x₁ (fresh-expand-ana1 (apart-extend1 Γ x₁ apt) frsh exp )
    fresh-expand-ana1 apt frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-expand-synth1 apt frsh x₃
    fresh-expand-ana1 apt FRHEHole EAEHole = FHole (EFId apt)
    fresh-expand-ana1 apt (FRHNEHole frsh) (EANEHole x₁ x₂) = FNEHole (EFId apt) (fresh-expand-synth1 apt frsh x₂)

  -- if x is fresh in the expansion of an hexp, it's fresh in that hexp
  mutual
    fresh-expand-synth2 : ∀{x e τ d Γ Δ} →
                         fresh x d →
                         Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         freshh x e
    fresh-expand-synth2 FConst ESConst = FRHConst
    fresh-expand-synth2 (FVar x₂) (ESVar x₃) = FRHVar x₂
    fresh-expand-synth2 (FLam x₂ frsh) (ESLam x₃ exp) = FRHLam2 x₂ (fresh-expand-synth2 frsh exp)
    fresh-expand-synth2 (FHole x₁) ESEHole = FRHEHole
    fresh-expand-synth2 (FNEHole x₁ frsh) (ESNEHole x₂ exp) = FRHNEHole (fresh-expand-synth2 frsh exp)
    fresh-expand-synth2 (FAp (FCast frsh) (FCast frsh₁)) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) =
                        FRHAp (fresh-expand-ana2 frsh x₅)
                              (fresh-expand-ana2 frsh₁ x₆)
    fresh-expand-synth2 (FCast frsh) (ESAsc x₁) = FRHAsc (fresh-expand-ana2 frsh x₁)

    fresh-expand-ana2 : ∀{ x e τ d τ' Γ Δ} →
                      fresh x d →
                      Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      freshh x e
    fresh-expand-ana2 (FLam x₁ frsh) (EALam x₂ x₃ exp) = FRHLam1 x₁ (fresh-expand-ana2 frsh exp)
    fresh-expand-ana2 frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-expand-synth2 frsh x₃
    fresh-expand-ana2 (FHole x₁) EAEHole = FRHEHole
    fresh-expand-ana2 (FNEHole x₁ frsh) (EANEHole x₂ x₃) = FRHNEHole (fresh-expand-synth2 frsh x₃)
