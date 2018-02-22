open import Prelude
open import core

module lemmas-ground where

  ground-arr-not-hole : ∀{τ1 τ2} →
                      (((τ1 ==> τ2) ground) → ⊥) →
                      ((τ1 ==> τ2) ≠ (⦇⦈ ==> ⦇⦈))
  ground-arr-not-hole notg refl = notg GHole
