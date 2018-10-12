open import Prelude
open import core

module grounding where
  matched-ground-invariant : ∀{ τ1 τ2} →
                             τ1 ▸gnd τ2 →
                             ((τ2 ground) × (τ1 ~ τ2) × (τ1 ≠ τ2))
  matched-ground-invariant (MGArr x) = GHole , TCArr TCHole1 TCHole1 , x
