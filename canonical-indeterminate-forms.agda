open import Nat
open import Prelude
open import contexts
open import core
open import type-assignment-unicity

module canonical-indeterminate-forms where
  canonical-indeterminate-forms-base : ∀{Δ d} →
                                       Δ , ∅ ⊢ d :: b →
                                       d indet →
                                       (Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ Γ' ∈ tctx ]
                                         ((d == ⦇⦈⟨ u , σ ⟩) ×
                                          ((u ::[ Γ' ] b) ∈ Δ))) +
                                       (Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ Γ' ∈ tctx ] Σ[ d' ∈ dhexp ] Σ[ τ' ∈ htyp ]
                                         ((d == ⦇ d' ⦈⟨ u , σ ⟩) ×
                                          (d' final) ×
                                          (Δ , ∅ ⊢ d' :: τ') ×
                                          ((u ::[ Γ' ] b) ∈ Δ))) +
                                       Σ[ d1 ∈ dhexp ] Σ[ d2 ∈ dhexp ] Σ[ τ2 ∈ htyp ] Σ[ d1' ∈ dhexp ]
                                         ((d == d1 ∘ d2) ×
                                          (Δ , ∅ ⊢ d1 :: τ2 ==> b) ×
                                          (Δ , ∅ ⊢ d2 :: τ2) ×
                                          (d1 indet) ×
                                          (d2 final) ×
                                          (d1 ≠ {!!}))
                                         +
                                       (Σ[ d' ∈ dhexp ] Σ[ d'' ∈ dhexp ] Σ[ τ' ∈ htyp ]
                                         ((d == d' ⟨ ⦇⦈ ⇒ b ⟩) ×
                                          (d' indet) ×
                                          (d' ≠ (d'' ⟨ τ' ⇒ ⦇⦈ ⟩))))
  canonical-indeterminate-forms-base TAConst ()
  canonical-indeterminate-forms-base (TAVar x₁) ()
  canonical-indeterminate-forms-base (TAAp wt wt₁) (IAp x ind x₁) = Inr (Inr (Inl (_ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , {!x!})))
  canonical-indeterminate-forms-base (TAEHole x x₁) IEHole = Inl (_ , _ , _ , refl , x)
  canonical-indeterminate-forms-base (TANEHole x wt x₁) (INEHole x₂) = Inr (Inl (_ , _ , _ , _ , _ , refl , x₂ , wt , x))
  canonical-indeterminate-forms-base (TACast wt x) (ICastHoleGround x₁ ind x₂) = Inr (Inr (Inr (_ , _ , _ , refl , ind , x₁)))

  -- canonical-indeterminate-forms-arr :
  -- canonical-indeterminate-forms-arr = ?

  -- canonical-indeterminate-forms-hole :
  -- canonical-indeterminate-forms-hole = ?

  canonical-indeterminate-forms-coverage : ∀{Δ d τ} →
                                           Δ , ∅ ⊢ d :: τ →
                                           d indet →
                                           τ ≠ b →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                           τ ≠ ⦇⦈ →
                                           ⊥
  canonical-indeterminate-forms-coverage TAConst () nb na nh
  canonical-indeterminate-forms-coverage (TAVar x₁) () nb na nh
  canonical-indeterminate-forms-coverage (TALam wt) () nb na nh
  canonical-indeterminate-forms-coverage (TAAp wt wt₁) (IAp x ind x₁) nb na nh = {!!}
  canonical-indeterminate-forms-coverage (TAEHole x x₁) IEHole nb na nh = {!!}
  canonical-indeterminate-forms-coverage (TANEHole x wt x₁) (INEHole x₂) nb na nh = {!!}
  canonical-indeterminate-forms-coverage (TACast wt x) (ICastArr x₁ ind) nb na nh = na _ _ refl
  canonical-indeterminate-forms-coverage (TACast wt x) (ICastGroundHole x₁ ind) nb na nh = nh refl
  canonical-indeterminate-forms-coverage (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh = {!!}
