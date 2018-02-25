open import Nat
open import Prelude
open import core

module confluence where
  confluence : ∀{d d1 d2} →
               d ↦* d1 →
               d ↦* d2 →
               Σ[ d' ∈ dhexp ] (d1 ↦* d' × d2 ↦* d')
  confluence = {!!}
