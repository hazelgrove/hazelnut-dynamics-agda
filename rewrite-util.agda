open import Prelude
open import core
open import Nat
open import contexts

module rewrite-util where

  rewrite-gamma : ∀{Δ Θ Γ Γ' d t} → Γ == Γ' → Δ , Θ , Γ ⊢ d :: t → Δ , Θ , Γ' ⊢ d :: t
  rewrite-gamma eq ta rewrite eq = ta

  rewrite-theta : ∀{Δ Θ Θ' Γ d t} → Θ == Θ' → Δ , Θ , Γ ⊢ d :: t → Δ , Θ' , Γ ⊢ d :: t
  rewrite-theta eq ta rewrite eq = ta

  rewrite-typ : ∀{Δ Θ Γ d t t'} → t == t' → Δ , Θ , Γ ⊢ d :: t → Δ , Θ , Γ ⊢ d :: t'
  rewrite-typ eq ta rewrite eq = ta

  forall-inj1 : ∀{t t' τ τ'} -> ·∀ t τ == ·∀ t' τ' -> t == t'
  forall-inj1 refl = refl
  forall-inj2 : ∀{t t' τ τ'} -> ·∀ t τ == ·∀ t' τ' -> τ == τ'
  forall-inj2 refl = refl
  typvar-inj : ∀{t t'} -> T t == T t' -> t == t'
  typvar-inj refl = refl

  rewrite-gamma-subst : ∀{Δ Θ Θf Γ Γ' Γf θ σ} → Γ == Γ' → Δ , Θ , Γ ⊢ θ , σ :s: Θf , Γf → Δ , Θ , Γ' ⊢ θ , σ :s: Θf , Γf
  rewrite-gamma-subst eq sub rewrite eq = sub
  
  rewrite-theta-subst : ∀{Δ Θ Θ' Θf Γ Γf θ σ} → Θ == Θ' → Δ , Θ , Γ ⊢ θ , σ :s: Θf , Γf → Δ , Θ' , Γ ⊢ θ , σ :s: Θf , Γf
  rewrite-theta-subst eq sub rewrite eq = sub
