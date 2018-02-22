open import Prelude
open import core

module lemmas-ground where
  ground-arr-not-hole : ∀{τ} →
                      (τ ground → ⊥) →
                      (τ ≠ (⦇⦈ ==> ⦇⦈))
  ground-arr-not-hole notg refl = notg GHole
