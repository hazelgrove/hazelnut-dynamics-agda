open import Prelude
open import core

module matched-ground-invariant where
  matched-ground-invariant : ∀{ τ τ'} →
                             τ ▸gnd τ' →
                             ((τ' ground) × (τ ~ τ') × (τ ≠ τ'))
  matched-ground-invariant (MGArr x) = GHole , TCArr TCHole1 TCHole1 , x
