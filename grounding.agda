open import Prelude
open import core

module grounding where
  grounding : ∀{ τ1 τ2} →
                             τ1 ▸gnd τ2 →
                             ((τ2 ground) × (τ1 ~ τ2) × (τ1 ≠ τ2))
  grounding (MGArr x) = GArr , TCArr TCHole1 TCHole1 , x
  grounding (MGForall x) = GForall , TCForall TCHole1 , {!   !}
