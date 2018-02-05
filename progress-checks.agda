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
-- be true at any time, i.e. that boxed values, indeterminates, cast
-- errors, and expressions that step are pairwise disjoint. (note that as a
-- consequence of currying and comutativity of products, this means that
-- there are six theorems to prove)
module progress-checks where
  -- boxed values and indeterminates are disjoint
  boxedval-not-indet : ∀{d} → d boxedval → d indet → ⊥
  boxedval-not-indet (BVVal VConst) ()
  boxedval-not-indet (BVVal VLam) ()
  boxedval-not-indet (BVArrCast x bv) (ICastArr x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVHoleCast x bv) (ICastGroundHole x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVHoleCast x bv) (ICastHoleGround x₁ ind x₂) = boxedval-not-indet bv ind

  -- boxed values and errors are disjoint
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

  -- boxed values and expressions that step are disjoint
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
    -- indeterminates and errors are disjoint
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

    -- final expressions are not errors (not one of the 6 cases for progress, just a convenience)
    final-not-err : ∀{d} → d final → d casterr → ⊥
    final-not-err (FBoxed x) err = boxedval-not-err x err
    final-not-err (FIndet x) err = indet-not-err x err

  -- todo: these are bad names; probably some places below where i inlined
  -- some of these lemmas before i'd come up with them
  lem2 : ∀{d d'} → d indet → d →> d' → ⊥
  lem2 IEHole ()
  lem2 (INEHole x) ()
  lem2 (IAp x₁ () x₂) (ITLam x₃)
  lem2 (IAp x (ICastArr x₁ ind) x₂) (ITApCast x₃ x₄) = x _ _ _ _ _ refl
  lem2 (ICastArr x ind) (ITCastID (FBoxed x₁)) = boxedval-not-indet x₁ ind
  lem2 (ICastArr x ind) (ITCastID (FIndet x₁)) = x refl
  lem2 (ICastGroundHole () ind) (ITCastID x₁)
  lem2 (ICastGroundHole x ind) (ITCastSucceed x₁ ())
  lem2 (ICastGroundHole GHole ind) (ITGround x₁ x₂) = x₂ refl
  lem2 (ICastHoleGround x ind ()) (ITCastID x₂)
  lem2 (ICastHoleGround x ind x₁) (ITCastSucceed x₂ x₃) = x _ _ refl
  lem2 (ICastHoleGround x ind GHole) (ITExpand x₂ x₃) = x₃ refl

  lem3 : ∀{d d'} → d boxedval → d →> d' → ⊥
  lem3 (BVVal VConst) ()
  lem3 (BVVal VLam) ()
  lem3 (BVArrCast x bv) (ITCastID x₁) = x refl
  lem3 (BVHoleCast () bv) (ITCastID x₁)
  lem3 (BVHoleCast () bv) (ITCastSucceed x₁ x₂)
  lem3 (BVHoleCast GHole bv) (ITGround x₁ y ) = y refl

  lem1 : ∀{d d'} → d final → d →> d' → ⊥
  lem1 (FBoxed x) = lem3 x
  lem1 (FIndet x) = lem2 x

  lem4 : ∀{d ε x} → d final → d == ε ⟦ x ⟧ → x final
  lem4 x FHOuter = x
  lem4 (FBoxed (BVVal ())) (FHAp1 eps)
  lem4 (FBoxed (BVVal ())) (FHAp2 x₂ eps)
  lem4 (FBoxed (BVVal ())) (FHNEHole eps)
  lem4 (FBoxed (BVVal ())) (FHCast eps)
  lem4 (FBoxed (BVArrCast x₁ x₂)) (FHCast eps) = lem4 (FBoxed x₂) eps
  lem4 (FBoxed (BVHoleCast x₁ x₂)) (FHCast eps) = lem4 (FBoxed x₂) eps
  lem4 (FIndet (IAp x₁ x₂ x₃)) (FHAp1 eps) = lem4 (FIndet x₂) eps
  lem4 (FIndet (IAp x₁ x₂ x₃)) (FHAp2 x₄ eps) = lem4 x₃ eps
  lem4 (FIndet (INEHole x₁)) (FHNEHole eps) = lem4 x₁ eps
  lem4 (FIndet (ICastArr x₁ x₂)) (FHCast eps) = lem4 (FIndet x₂) eps
  lem4 (FIndet (ICastGroundHole x₁ x₂)) (FHCast eps) = lem4 (FIndet x₂) eps
  lem4 (FIndet (ICastHoleGround x₁ x₂ x₃)) (FHCast eps) = lem4 (FIndet x₂) eps

  lem5 : ∀{d d' d'' ε} →  d final → d == ε ⟦ d' ⟧ → d' →> d'' → ⊥
  lem5 f sub step = lem1 (lem4 f sub) step

  -- indeterminates and expressions that step are disjoint
  mutual
    indet-not-step : ∀{d} → d indet → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
    indet-not-step IEHole (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = lem5 x x₁ x₂
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

    final-not-step : ∀{d} → d final → Σ[ d' ∈ dhexp ] (d ↦ d') → ⊥
    final-not-step (FBoxed x) stp = boxedval-not-step x stp
    final-not-step (FIndet x) stp = indet-not-step x stp

  -- errors and expressions that step are disjoint
  err-not-step : ∀{d} → d casterr → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
    -- cast fail caserr-not-step
  err-not-step (CECastFail x x₁ () x₃) (_ , Step FHOuter (ITCastID x₄) FHOuter)
  err-not-step (CECastFail x x₁ x₂ x₃) (_ , Step FHOuter (ITCastSucceed x₄ x₅) FHOuter) = x₃ refl
  err-not-step (CECastFail x x₁ GHole x₃) (_ , Step FHOuter (ITExpand x₄ x₅) FHOuter) = x₅ refl
  err-not-step (CECastFail x x₁ x₂ x₃) (_ , Step (FHCast x₄) x₅ (FHCast x₆)) = {!!}

    -- congruence caserr-not-step
  err-not-step (CECong FHOuter ce) (π1 , Step FHOuter x₂ FHOuter) = err-not-step ce (π1 , Step FHOuter x₂ FHOuter)
  err-not-step (CECong (FHAp1 FHOuter) (CECong FHOuter ce)) (_ , Step FHOuter (ITLam x₂) FHOuter) = boxedval-not-err (BVVal VLam) ce
  err-not-step (CECong (FHAp1 x) ce) (_ , Step FHOuter (ITApCast x₁ x₂) FHOuter) = {!!}  -- fe x₁ (CECong {!ce-out-cast ce!} ce)
  err-not-step (CECong (FHAp2 x x₁) ce) (π1 , Step FHOuter x₂ FHOuter) = {!ce-out-cast ce x₁!}
  err-not-step (CECong (FHNEHole x) ce) (π1 , Step FHOuter x₂ FHOuter) = {!!}
  err-not-step (CECong (FHCast x) ce) (π1 , Step FHOuter x₂ FHOuter) = {!!}

  err-not-step (CECong FHOuter ce) (_ , Step (FHAp1 x₁) x₂ (FHAp1 x₃))
    with ce-ap ce
  ... | Inl d1err = err-not-step d1err (_ , Step x₁ x₂ x₃)
  ... | Inr d2err = {!Step x₁ x₂ x₃!} -- this is a counter example: d2 is a casterror but d1 isn't yet a value so the whole thing steps
  err-not-step (CECong (FHAp1 x) ce) (_ , Step (FHAp1 x₁) x₂ (FHAp1 x₃)) = err-not-step (ce-out-cast ce x) (_ , Step x₁ x₂ x₃)
  err-not-step (CECong (FHAp2 x x₁) ce) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = final-not-step x (_ , Step x₂ x₃ x₄)

  err-not-step (CECong FHOuter ce) (_ , Step (FHAp2 x₁ x₂) x₃ (FHAp2 x₄ x₅))
    with ce-ap ce
  ... | Inl d1err = final-not-err x₄ d1err
  ... | Inr d2err = err-not-step d2err (_ , Step x₂ x₃ x₅)
  err-not-step (CECong (FHAp1 x) ce) (_ , Step (FHAp2 x₁ x₂) x₃ (FHAp2 x₄ x₅)) = {!!}
  err-not-step (CECong (FHAp2 x x₁) ce) (_ , Step (FHAp2 x₂ x₃) x₄ (FHAp2 x₅ x₆)) = {!!}

  err-not-step (CECong FHOuter ce) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = err-not-step (ce-nehole ce) (_ , Step x₁ x₂ x₃)
  err-not-step (CECong (FHNEHole x) ce) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = err-not-step (ce-out-cast ce x) (_ , Step x₁ x₂ x₃)

  err-not-step (CECong FHOuter ce) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = {!!} -- err-not-step {!!} (_ , Step x₁ x₂ x₃) -- this might not work
  err-not-step (CECong (FHCast x) ce) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = err-not-step (ce-out-cast ce x) (_ , Step x₁ x₂ x₃)
