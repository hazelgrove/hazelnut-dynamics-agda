open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-consistency
open import type-assignment-unicity
open import lemmas-progress-checks

-- taken together, the theorems in this file argue that for any expression
-- d, at most one summand of the labeled sum that results from progress may
-- be true at any time: that boxed values, indeterminates, and expressions
-- that step are pairwise disjoint.
--
-- note that as a consequence of currying and comutativity of products,
-- this means that there are three theorems to prove. in addition to those,
-- we also prove several convenince forms that combine theorems about
-- indeterminate and boxed value forms into the same statement about final
-- forms, which mirrors the mutual definition of indeterminate and final
-- and saves some redundant argumentation.
module progress-checks where
  -- boxed values are not indeterminates
  boxedval-not-indet : ∀{d} → d boxedval → d indet → ⊥
  boxedval-not-indet (BVVal VConst) ()
  boxedval-not-indet (BVVal VLam) ()
  boxedval-not-indet (BVArrCast x bv) (ICastArr x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVForallCast x bv) (ICastForall x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVHoleCast x bv) (ICastGroundHole x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVHoleCast x bv) (ICastHoleGround x₁ ind x₂) = boxedval-not-indet bv ind

  -- boxed values don't step
  boxedval-not-step : ∀{d} → d boxedval → (Σ[ d' ∈ ihexp ] (d ↦ d')) → ⊥
  boxedval-not-step (BVVal VConst) (d' , Step FHOuter () x₃)
  boxedval-not-step (BVVal VLam) (d' , Step FHOuter () x₃)
  boxedval-not-step (BVArrCast x bv) (d0' , Step FHOuter (ITCastID) FHOuter) = x refl
  boxedval-not-step (BVArrCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVForallCast x bv) (_ , Step FHOuter (ITCastID) FHOuter) = x refl
  boxedval-not-step (BVForallCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVHoleCast () bv) (d' , Step FHOuter (ITCastID) FHOuter)
  boxedval-not-step (BVHoleCast x bv) (d' , Step FHOuter (ITCastSucceed ()) FHOuter)
  boxedval-not-step (BVHoleCast GArr bv) (_ , Step FHOuter (ITGround (MGArr x)) FHOuter) = x refl
  boxedval-not-step (BVHoleCast GForall bv) (_ , Step FHOuter (ITGround (MGForall x)) FHOuter) = x refl
  boxedval-not-step (BVHoleCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVHoleCast x x₁) (_ , Step FHOuter (ITExpand ()) FHOuter)
  boxedval-not-step (BVHoleCast x x₁) (_ , Step FHOuter (ITCastFail x₂ () x₄) FHOuter)

  mutual
    -- indeterminates don't step
    indet-not-step : ∀{d} → d indet → (Σ[ d' ∈ ihexp ] (d ↦ d')) → ⊥
    indet-not-step IEHole (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = final-sub-not-trans x x₁ x₂
    indet-not-step (IAp x₁ () x₂) (_ , Step FHOuter (ITLam) FHOuter)
    indet-not-step (IAp x (ICastArr x₁ ind) x₂) (_ , Step FHOuter (ITApCast) FHOuter) = x _ _ _ _ _  refl
    indet-not-step (IAp x ind _) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = indet-not-step ind (_ , Step x₂ x₃ x₄)
    indet-not-step (IAp x ind f) (_ , Step (FHAp2 x₃) x₄ (FHAp2 x₆)) = final-not-step f (_ , Step x₃ x₄ x₆)
    indet-not-step (ITAp x ind) (_ , Step FHOuter (ITTApCast) FHOuter) = x _ _ _  refl
    indet-not-step (ITAp x ind) (_ , Step (FHTAp x₂) x₃ (FHTAp x₄)) = indet-not-step ind (_ , Step x₂ x₃ x₄)
    indet-not-step (ICastArr x ind) (d0' , Step FHOuter (ITCastID) FHOuter) = x refl
    indet-not-step (ICastArr x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastForall x ind) (d0' , Step FHOuter (ITCastID) FHOuter) = x refl
    indet-not-step (ICastForall x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastGroundHole () ind) (d' , Step FHOuter (ITCastID) FHOuter)
    indet-not-step (ICastGroundHole x ind) (d' , Step FHOuter (ITCastSucceed ()) FHOuter)
    indet-not-step (ICastGroundHole GArr ind) (_ , Step FHOuter (ITGround (MGArr x₁)) FHOuter) = x₁ refl
    indet-not-step (ICastGroundHole GForall ind) (_ , Step FHOuter (ITGround (MGForall x₁)) FHOuter) = x₁ refl
    indet-not-step (ICastGroundHole x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastHoleGround x ind ()) (d' , Step FHOuter (ITCastID ) FHOuter)
    indet-not-step (ICastHoleGround x ind g) (d' , Step FHOuter (ITCastSucceed  x₂) FHOuter) = x _ _ refl
    indet-not-step (ICastHoleGround x ind GArr) (_ , Step FHOuter (ITExpand (MGArr x₂)) FHOuter) = x₂ refl
    indet-not-step (ICastHoleGround x ind GForall) (_ , Step FHOuter (ITExpand (MGForall x₂)) FHOuter) = x₂ refl
    indet-not-step (ICastHoleGround x ind g) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastGroundHole x x₁) (_ , Step FHOuter (ITExpand ()) FHOuter)
    indet-not-step (ICastHoleGround x x₁ x₂) (_ , Step FHOuter (ITGround ()) FHOuter)
    indet-not-step (ICastGroundHole x x₁) (_ , Step FHOuter (ITCastFail x₂ () x₄) FHOuter)
    indet-not-step (ICastHoleGround x x₁ x₂) (_ , Step FHOuter (ITCastFail x₃ x₄ x₅) FHOuter) = x _ _ refl
    indet-not-step (IFailedCast x x₁ x₂ x₃) (d' , Step FHOuter () FHOuter)
    indet-not-step (IFailedCast x x₁ x₂ x₃) (_ , Step (FHFailedCast x₄) x₅ (FHFailedCast x₆)) = final-not-step x (_ , Step x₄ x₅ x₆)

    -- final expressions don't step
    final-not-step : ∀{d} → d final → Σ[ d' ∈ ihexp ] (d ↦ d') → ⊥
    final-not-step (FBoxedVal x) stp = boxedval-not-step x stp
    final-not-step (FIndet x) stp = indet-not-step x stp
