open import Prelude
open import core

module finality where
  -- todo: this will come from progress checks, once that's all squared away
  postulate
    fs : ∀{d} → d final → Σ[ d' ∈ dhexp ] (d ↦ d') → ⊥

  finality : ∀{d d'} → d final → d ↦* d' → d == d'
  finality fin MSRefl = refl
  finality fin (MSStep x ms) = abort (fs fin (_ , x))
