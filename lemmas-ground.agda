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
  ground-forall-not-hole : ∀{τ} →
                      (τ ground → ⊥) →
                      (τ ≠ (·∀ ⦇-⦈))
  ground-forall-not-hole notg refl = notg GForall

  -- not ground types either have to be hole, a type variable, an arrow, or a forall
  notground : ∀{τ} → 
              (τ ground → ⊥) → 
              (τ == ⦇-⦈) 
              + (Σ[ x ∈ Nat ] (τ == (T x)))
              + (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] (τ == (τ1 ==> τ2)))
              + (Σ[ τ1 ∈ htyp ] (τ == (·∀ τ1)))
  notground {b} gnd = abort (gnd GBase)
  notground {⦇-⦈} gnd = Inl refl
  notground {T x} gnd = Inr (Inl (x , refl))
  notground {τ1 ==> τ2} gnd = Inr (Inr (Inl (τ1 , τ2 , refl)))
  notground {·∀ τ} gnd = Inr (Inr (Inr (τ , refl)))

