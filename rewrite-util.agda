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

  forall-eq : ∀{t t' τ τ'} -> t == t' -> τ == τ' -> ·∀ t τ == ·∀ t' τ'
  forall-eq eq1 eq2 rewrite eq1 rewrite eq2 = refl

  arr-eq : ∀{τ1 τ1' τ2 τ2'} -> τ1 == τ1' -> τ2 == τ2' -> τ1 ==> τ2 == τ1' ==> τ2'
  arr-eq eq1 eq2 rewrite eq1 rewrite eq2 = refl

  rewrite-gamma-subst : ∀{Δ Θ Θf Γ Γ' Γf θ σ} → Γ == Γ' → Δ , Θ , Γ ⊢ θ , σ :s: Θf , Γf → Δ , Θ , Γ' ⊢ θ , σ :s: Θf , Γf
  rewrite-gamma-subst eq sub rewrite eq = sub
  
  rewrite-theta-subst : ∀{Δ Θ Θ' Θf Γ Γf θ σ} → Θ == Θ' → Δ , Θ , Γ ⊢ θ , σ :s: Θf , Γf → Δ , Θ' , Γ ⊢ θ , σ :s: Θf , Γf
  rewrite-theta-subst eq sub rewrite eq = sub

  some-epi : {A : Set} -> {x y : A} ->
    x == y -> Some x == Some y
  some-epi eq rewrite eq = refl

  forall-sub-neq : ∀{t t' τ τ'} -> (t == t' → ⊥) -> Typ[ τ / t ] (·∀ t' τ') == ·∀ t' (Typ[ τ / t ] τ')
  forall-sub-neq {t} {t'} neq with natEQ t t'
  ... | Inl refl = abort (neq refl)
  ... | Inr neq' = refl

  forall-sub-eq : ∀{t t' τ τ'} -> t == t' -> Typ[ τ / t ] (·∀ t' τ') == ·∀ t' τ'
  forall-sub-eq {t} {t'} eq with natEQ t t'
  ... | Inl refl = refl
  ... | Inr neq = abort (neq eq)
