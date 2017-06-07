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

  ▸sum-unicity : ∀{ t t2 t3 } →
                 t ▸sum t2 →
                 t ▸sum t3 →
                 t2 == t3
  ▸sum-unicity MSHole MSHole = refl
  ▸sum-unicity MSPlus MSPlus = refl

  ▸pro-unicity : ∀{ t t2 t3 } →
                 t ▸pro t2 →
                 t ▸pro t3 →
                 t2 == t3
  ▸pro-unicity MPHole MPHole = refl
  ▸pro-unicity MPPlus MPPlus = refl


  -- if an arrow matches, then it's consistent with the least restrictive
  -- function type
  matchconsist : ∀{t t'} →
                 t ▸arr t' →
                 t ~ (⦇⦈ ==> ⦇⦈)
  matchconsist MAHole = TCHole2
  matchconsist MAArr = TCArr TCHole1 TCHole1

  matchnotnum : ∀{t1 t2} → num ▸arr (t1 ==> t2) → ⊥
  matchnotnum ()
