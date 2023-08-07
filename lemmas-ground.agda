open import Nat
open import Prelude
open import core

module lemmas-ground where
  -- not ground types aren't hole to hole
  ground-arr-not-hole : ∀{τ} →
                      (τ ground → ⊥) →
                      (τ ≠ (⦇-⦈ ==> ⦇-⦈))
  ground-arr-not-hole notg refl = notg GArr

  -- not ground types aren't forall hole
  ground-forall-not-hole : ∀{t τ} →
                      (τ ground → ⊥) →
                      (τ ≠ (·∀ t ⦇-⦈))
  ground-forall-not-hole notg refl = notg GForall

  -- not ground types either have to be hole, a type variable, an arrow, or a forall
  notground : ∀{τ} → 
              (τ ground → ⊥) → 
              (τ == ⦇-⦈) 
              + (Σ[ x ∈ Nat ] (τ == (T x)))
              + (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] (τ == (τ1 ==> τ2)))
              + (Σ[ t ∈ Nat ] Σ[ τ1 ∈ htyp ] (τ == (·∀ t τ1)))
  notground {b} gnd = abort (gnd GBase)
  notground {⦇-⦈} gnd = Inl refl
  notground {T x} gnd = Inr (Inl (x , refl))
  notground {τ1 ==> τ2} gnd = Inr (Inr (Inl (τ1 , τ2 , refl)))
  notground {·∀ t τ} gnd = Inr (Inr (Inr (t , τ , refl)))

  ground-subst-id : ∀{t τ1 τ2} -> τ1 ground -> (Typ[ τ2 / t ] τ1) == τ1
  ground-subst-id GBase = refl
  ground-subst-id GArr = refl
  ground-subst-id {t = t} (GForall {t = t'}) with natEQ t t'
  ... | Inl refl = refl
  ... | Inr neq = refl

  ground-subst : ∀{t τ1 τ2} -> τ1 ground -> (Typ[ τ2 / t ] τ1) ground
  ground-subst {t} {τ1} {τ2} g rewrite ground-subst-id {t} {τ1} {τ2} g = g
