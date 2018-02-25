open import Prelude
open import core

open import progress-checks

module finality where
  finality : ∀{d d'} → d final → d ↦* d' → d == d'
  finality fin MSRefl = refl
  finality fin (MSStep x ms) = abort (final-not-step fin (_ , x))
