open import Nat
open import Prelude
open import List
open import core
open import contexts

module canonical-forms where
  cf-lam : ∀{Δ Γ d τ1 τ2 } →
            Δ , Γ ⊢ d :: (τ1 ==> τ2) →
            d val →
            Σ[ x ∈ Nat ] Σ[ d' ∈ dhexp ] (d == (·λ_[_]_ x τ1 d'))
  cf-lam (TAVar x₁) ()
  cf-lam (TALam D) VLam = _ , _ , refl
  cf-lam (TAAp D x D₁) ()
  cf-lam (TAEHole x x₁) ()
  cf-lam (TANEHole x D x₁) ()
  cf-lam (TACast D x) ()

  cf-base : ∀{ Δ d Γ } →
            Δ , Γ ⊢ d :: b →
            d val →
            d == c
  cf-base TAConst VConst = refl
  cf-base (TAVar x₁) ()
  cf-base (TAAp D x D₁) ()
  cf-base (TAEHole x x₁) ()
  cf-base (TANEHole x D x₁) ()
  cf-base (TACast D x) ()
