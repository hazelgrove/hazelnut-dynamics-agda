open import Nat
open import Prelude
open import core

module commutativity where
  commutativity : ∀{d0 d1 d u} →
                  -- probably need a premise that d0 is well typed
                  d0 ↦* d1 →
                  (⟦ d / u ⟧ d0) ↦* (⟦ d / u ⟧ d1)
  commutativity MSRefl = MSRefl
  commutativity (MSStep x stp) with commutativity stp
  ... | ih = MSStep {!!} {!!}
