open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core

module debruijn.debruijn-lemmas-ground where

  ground-arr-not-hole : ∀{τ} →
    (τ ground → ⊥) →
    (τ ≠ (⦇-⦈ ==> ⦇-⦈))
  ground-arr-not-hole notg refl = notg GArr

  ground-forall-not-hole : ∀{τ} →
    (τ ground → ⊥) →
    (τ ≠ (·∀ ⦇-⦈))
  ground-forall-not-hole notg refl = notg GForall

  ground-neq~ : ∀{τ1 τ2} → τ1 ground → τ2 ground → τ1 ≠ τ2 → τ1 ~̸ τ2
  ground-neq~ GBase GBase neq = λ _ → neq refl 
  ground-neq~ GBase GArr neq = λ ()
  ground-neq~ GBase GForall neq = λ ()
  ground-neq~ GArr GBase neq = λ ()
  ground-neq~ GArr GArr neq = λ _ → neq refl
  ground-neq~ GArr GForall neq = λ ()
  ground-neq~ GForall GBase neq = λ ()
  ground-neq~ GForall GArr neq = λ ()
  ground-neq~ GForall GForall neq = λ _ → neq refl