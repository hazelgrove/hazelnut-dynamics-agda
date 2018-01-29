open import Prelude
open import core

module lemmas-matching where
  -- matching produces unique answers for arrows, sums, and products
  ▸arr-unicity : ∀{ t t2 t3 } →
                 t ▸arr t2 →
                 t ▸arr t3 →
                 t2 == t3
  ▸arr-unicity MAHole MAHole = refl
  ▸arr-unicity MAArr MAArr = refl

  -- if an arrow matches, then it's consistent with the least restrictive
  -- function type
  matchconsisthole : ∀{t t'} →
                 t ▸arr t' →
                 t ~ (⦇⦈ ==> ⦇⦈)
  matchconsisthole MAHole = TCHole2
  matchconsisthole MAArr = TCArr TCHole1 TCHole1

  match-consist : ∀{τ1 τ2} → τ1 ▸arr τ2 → (τ2 ~ τ1)
  match-consist MAHole = TCHole1
  match-consist MAArr = TCRefl
