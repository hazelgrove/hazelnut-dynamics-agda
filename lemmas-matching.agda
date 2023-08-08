open import Prelude
open import core
open import lemmas-consistency

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
                 t ~ (⦇-⦈ ==> ⦇-⦈)
  matchconsisthole MAHole = TCHole2
  matchconsisthole MAArr = TCArr TCHole1 TCHole1

  match-consist : ∀{τ1 τ2} → τ1 ▸arr τ2 → (τ2 ~ τ1)
  match-consist MAHole = TCHole1
  match-consist (MAArr {τ1} {τ2}) = ~refl

  -- match-unicity : ∀{ τ τ1 τ2} → τ ▸arr τ1 → τ ▸arr τ2 → τ1 == τ2
  -- match-unicity MAHole MAHole = refl
  -- match-unicity MAArr MAArr = refl

  -- matching produces unique answers for arrows, sums, and products
  ▸forall-unicity : ∀{ t t2 t3 } →
                 t ▸forall t2 →
                 t ▸forall t3 →
                 t2 == t3
  ▸forall-unicity MFHole MFHole = {!   !}
  ▸forall-unicity MFForall MFForall = refl

  -- if an arrow matches, then it's consistent with the least restrictive
  -- function type
  forall-matchconsisthole : ∀{t t' tvar} →
                 t ▸forall t' →
                 t ~ (·∀ tvar ⦇-⦈)
  forall-matchconsisthole MFHole = TCHole2
  forall-matchconsisthole MFForall = {! TCForall TCHole1 !}

  forall-match-consist : ∀{τ1 τ2} → τ1 ▸forall τ2 → (τ2 ~ τ1)
  forall-match-consist MFHole = TCHole1
  forall-match-consist (MFForall {τ}) = ~refl

  -- forall-match-unicity : ∀{ τ τ1 τ2} → τ ▸forall τ1 → τ ▸forall τ2 → τ1 == τ2
  -- forall-match-unicity MFHole MFHole = refl
  -- forall-match-unicity MFForall MFForall = refl
