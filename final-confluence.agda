open import Nat
open import Prelude
open import core

open import finality

module final-confluence where
  -- todo
  postulate
      confluence : ∀{d d1 d2} →
               d ↦* d1 →
               d ↦* d2 →
               Σ[ d' ∈ dhexp ] (d1 ↦* d' × d2 ↦* d')

  final-confluence : ∀{d d1 d2} →
                     d ↦* d1 →
                     d1 final →
                     d ↦* d2 →
                     d2 ↦* d1
  final-confluence s1 f s2 with confluence s1 s2
  ... | d' , st1 , st2 with finality f st1
  ... | refl = st2
