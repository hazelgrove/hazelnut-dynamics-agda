open import Nat
open import Prelude
open import core

open import final-confluence

module resumption where
  postulate
    commutativity : ∀{d0 d1 d u} →
                  -- probably need a premise that d0 is well typed
                  d0 ↦* d1 →
                  (⟦ d / u ⟧ d0) ↦* (⟦ d / u ⟧ d1)

  resumption : ∀ {d1 d2 d3 d4 u} →
               d1 ↦* d2 →
               d2 final →
               (⟦ d3 / u ⟧ d1) ↦* d4 →
               d4 final →
               (⟦ d3 / u ⟧ d2) ↦* d4
  resumption st1 f1 st2 f2 = final-confluence st2 f2 (commutativity st1)
