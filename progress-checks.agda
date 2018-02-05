open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency
open import type-assignment-unicity
open import lemmas-progress-checks

-- taken together, the theorems in this file argue that for any expression
-- d, at most one summand of the labeled sum that results from progress may
-- be true at any time: that boxed values, indeterminates, cast errors, and
-- expressions that step are pairwise disjoint.
--
-- note that as a consequence of currying and comutativity of products,
-- this means that there are six theorems to prove. in addition to those,
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
  boxedval-not-indet (BVHoleCast x bv) (ICastGroundHole x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVHoleCast x bv) (ICastHoleGround x₁ ind x₂) = boxedval-not-indet bv ind

  -- boxed values are not errors
  boxedval-not-err : ∀{d} → d boxedval → d casterr → ⊥
  boxedval-not-err (BVVal ()) (CECastFail x₁ x₂ x₃ x₄)
  boxedval-not-err (BVHoleCast x bv) (CECastFail x₁ x₂ () x₄)
  boxedval-not-err (BVArrCast x bv) (CECong FHOuter er) = boxedval-not-err bv (ce-castarr er)
  boxedval-not-err (BVArrCast x bv) (CECong (FHCast x₁) er) = boxedval-not-err bv (CECong x₁ er)
  boxedval-not-err (BVHoleCast x bv) (CECong FHOuter er) = boxedval-not-err bv (ce-castth er)
  boxedval-not-err (BVHoleCast x bv) (CECong (FHCast x₁) er) = boxedval-not-err bv (CECong x₁ er)
  boxedval-not-err (BVVal x) (CECong FHOuter er) = boxedval-not-err (BVVal x) er
  boxedval-not-err (BVVal ()) (CECong (FHAp1 x₁) er)
  boxedval-not-err (BVVal ()) (CECong (FHAp2 x₁ x₂) er)
  boxedval-not-err (BVVal ()) (CECong (FHNEHole x₁) er)
  boxedval-not-err (BVVal ()) (CECong (FHCast x₁) er)

  -- boxed values don't step
  boxedval-not-step : ∀{d} → d boxedval → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  boxedval-not-step (BVVal VConst) (d' , Step FHOuter () x₃)
  boxedval-not-step (BVVal VLam) (d' , Step FHOuter () x₃)
  boxedval-not-step (BVArrCast x bv) (d0' , Step FHOuter (ITCastID x₁) FHOuter) = x refl
  boxedval-not-step (BVArrCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVHoleCast () bv) (d' , Step FHOuter (ITCastID x₁) FHOuter)
  boxedval-not-step (BVHoleCast x bv) (d' , Step FHOuter (ITCastSucceed x₁ ()) FHOuter)
  boxedval-not-step (BVHoleCast GHole bv) (_ , Step FHOuter (ITGround x₁ x₂) FHOuter) = x₂ refl
  boxedval-not-step (BVHoleCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)

  -- todo: what class of P is this true for?
  -- lem-something : ∀{ d ε d'} → d == ε ⟦ d' ⟧ → P d' → P d

  mutual
    -- indeterminates are not errors
    indet-not-err : ∀{d} → d indet → d casterr → ⊥
    indet-not-err IEHole (CECong FHOuter err) = indet-not-err IEHole err
    indet-not-err (INEHole x) (CECong FHOuter err) = final-not-err x (ce-nehole err)
    indet-not-err (INEHole x) (CECong (FHNEHole x₁) err) = final-not-err x (CECong x₁ err)
    indet-not-err (IAp x indet x₁) (CECong FHOuter err)
      with ce-ap err
    ... | Inl d1err = indet-not-err indet d1err
    ... | Inr d2err = final-not-err x₁ d2err
    indet-not-err (IAp x indet x₁) (CECong (FHAp1 x₂) err) = indet-not-err indet (CECong x₂ err)
    indet-not-err (IAp x indet x₁) (CECong (FHAp2 x₂ x₃) err) = final-not-err x₁ (CECong x₃ err)
    indet-not-err (ICastArr x indet) (CECong FHOuter err) = indet-not-err indet (ce-castarr err)
    indet-not-err (ICastArr x indet) (CECong (FHCast x₁) err) = indet-not-err indet (CECong x₁ err)
    indet-not-err (ICastGroundHole x indet) (CECastFail x₁ x₂ () x₄)
    indet-not-err (ICastGroundHole x indet) (CECong FHOuter err) = indet-not-err indet (ce-castth err)
    indet-not-err (ICastGroundHole x indet) (CECong (FHCast x₁) err) = indet-not-err indet (CECong x₁ err)
    indet-not-err (ICastHoleGround x indet x₁) (CECastFail x₂ x₃ x₄ x₅) = x _ _ refl
    indet-not-err (ICastHoleGround x indet x₁) (CECong FHOuter err) = indet-not-err indet (ce-castht err x)
    indet-not-err (ICastHoleGround x indet x₁) (CECong (FHCast x₂) err) = indet-not-err indet (CECong x₂ err)

    -- final expressions are not errors
    final-not-err : ∀{d} → d final → d casterr → ⊥
    final-not-err (FBoxed x) err = boxedval-not-err x err
    final-not-err (FIndet x) err = indet-not-err x err

  mutual
    -- indeterminates don't step
    indet-not-step : ∀{d} → d indet → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
    indet-not-step IEHole (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = final-sub-not-trans x x₁ x₂
    indet-not-step (IAp x₁ () x₂) (_ , Step FHOuter (ITLam x₃) FHOuter)
    indet-not-step (IAp x (ICastArr x₁ ind) x₂) (_ , Step FHOuter (ITApCast x₃ x₄) FHOuter) = x _ _ _ _ _  refl
    indet-not-step (IAp x ind _) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = indet-not-step ind (_ , Step x₂ x₃ x₄)
    indet-not-step (IAp x ind f) (_ , Step (FHAp2 x₂ x₃) x₄ (FHAp2 x₅ x₆)) = final-not-step f (_ , Step x₃ x₄ x₆)
    indet-not-step (ICastArr x ind) (d0' , Step FHOuter (ITCastID x₁) FHOuter) = x refl
    indet-not-step (ICastArr x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastGroundHole () ind) (d' , Step FHOuter (ITCastID x₁) FHOuter)
    indet-not-step (ICastGroundHole x ind) (d' , Step FHOuter (ITCastSucceed x₁ ()) FHOuter)
    indet-not-step (ICastGroundHole GHole ind) (_ , Step FHOuter (ITGround _ y) FHOuter) = y refl
    indet-not-step (ICastGroundHole x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastHoleGround x ind ()) (d' , Step FHOuter (ITCastID x₁) FHOuter)
    indet-not-step (ICastHoleGround x ind g) (d' , Step FHOuter (ITCastSucceed x₁ x₂) FHOuter) = x _ _ refl
    indet-not-step (ICastHoleGround x ind GHole) (_ , Step FHOuter (ITExpand x₁ x₂) FHOuter) = x₂ refl
    indet-not-step (ICastHoleGround x ind g) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)

    -- final expressions don't step
    final-not-step : ∀{d} → d final → Σ[ d' ∈ dhexp ] (d ↦ d') → ⊥
    final-not-step (FBoxed x) stp = boxedval-not-step x stp
    final-not-step (FIndet x) stp = indet-not-step x stp

  -- errors don't step
  err-not-step : ∀{d} → d casterr → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
    -- cast fail cases
  err-not-step (CECastFail x x₁ () x₃) (_ , Step FHOuter (ITCastID x₄) FHOuter)
  err-not-step (CECastFail x x₁ x₂ x₃) (_ , Step FHOuter (ITCastSucceed x₄ x₅) FHOuter) = x₃ refl
  err-not-step (CECastFail x x₁ GHole x₃) (_ , Step FHOuter (ITExpand x₄ x₅) FHOuter) = x₅ refl
  err-not-step (CECastFail x () x₂ x₃) (_ , Step (FHCast FHOuter) (ITCastID x₄) (FHCast FHOuter))
  err-not-step (CECastFail x () x₂ x₃) (_ , Step (FHCast FHOuter) (ITCastSucceed x₄ x₅) (FHCast FHOuter))
  err-not-step (CECastFail x GHole x₂ x₃) (_ , Step (FHCast FHOuter) (ITGround x₄ x₅) (FHCast FHOuter)) = x₅ refl
  err-not-step (CECastFail x x₁ x₂ x₃) (_ , Step (FHCast (FHCast x₄)) x₅ (FHCast (FHCast x₆))) = final-not-step x (_ , Step x₄ x₅ x₆)

    -- congruence cases
  err-not-step (CECong FHOuter ce) (π1 , Step FHOuter x₂ FHOuter) = err-not-step ce (π1 , Step FHOuter x₂ FHOuter)
  err-not-step (CECong (FHAp1 FHOuter) (CECong FHOuter ce)) (_ , Step FHOuter (ITLam x₂) FHOuter) = boxedval-not-err (BVVal VLam) ce
  err-not-step (CECong (FHAp1 x) ce) (_ , Step FHOuter (ITApCast x₁ x₂) FHOuter) = {!!} -- final-not-err x₁ (CECong {!!} ce) -- proably case on x, but get incomplete pattern garbage
  err-not-step (CECong (FHAp2 x x₁) ce) (π1 , Step FHOuter x₂ FHOuter) = {!!} -- cyrus: possibly another counter example
  err-not-step (CECong (FHNEHole x) ce) (π1 , Step FHOuter () FHOuter)
  err-not-step (CECong (FHCast x) ce) (π1 , Step FHOuter x₂ FHOuter) = {!!} -- cyrus: only obvious thing to do is case on x₂, doesn't seem to get anywhere

  err-not-step (CECong FHOuter ce) (_ , Step (FHAp1 x₁) x₂ (FHAp1 x₃))
    with ce-ap ce
  ... | Inl d1err = err-not-step d1err (_ , Step x₁ x₂ x₃)
  ... | Inr d2err = {!Step x₁ x₂ x₃!} -- cyrus: this is a counter example, d2 is a casterror but d1 isn't yet a value so the whole thing steps
  err-not-step (CECong (FHAp1 x) ce) (_ , Step (FHAp1 x₁) x₂ (FHAp1 x₃)) = err-not-step (ce-out-cast ce x) (_ , Step x₁ x₂ x₃)
  err-not-step (CECong (FHAp2 x x₁) ce) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = final-not-step x (_ , Step x₂ x₃ x₄)

  err-not-step (CECong FHOuter ce) (_ , Step (FHAp2 x₁ x₂) x₃ (FHAp2 x₄ x₅))
    with ce-ap ce
  ... | Inl d1err = final-not-err x₄ d1err
  ... | Inr d2err = err-not-step d2err (_ , Step x₂ x₃ x₅)
  err-not-step (CECong (FHAp1 x) ce) (_ , Step (FHAp2 x₁ x₂) x₃ (FHAp2 x₄ x₅)) = final-not-err x₁ (ce-out-cast ce x)
  err-not-step (CECong (FHAp2 x x₁) ce) (_ , Step (FHAp2 x₂ x₃) x₄ (FHAp2 x₅ x₆)) = err-not-step (ce-out-cast ce x₁) (_ , Step x₃ x₄ x₆)

  err-not-step (CECong FHOuter ce) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = err-not-step (ce-nehole ce) (_ , Step x₁ x₂ x₃)
  err-not-step (CECong (FHNEHole x) ce) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = err-not-step (ce-out-cast ce x) (_ , Step x₁ x₂ x₃)

  err-not-step (CECong FHOuter ce) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = {!!} -- cyrus not sure how to proceed at all; obvious lemma is probably false
  err-not-step (CECong (FHCast x) ce) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = err-not-step (ce-out-cast ce x) (_ , Step x₁ x₂ x₃)
