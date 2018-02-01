open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency
open import type-assignment-unicity

-- taken together, the theorems in this file argue that for any expression
-- d, at most one summand of the labeled sum that results from progress may
-- be true at any time, i.e. that values, indeterminates, errors, and
-- expressions that step are pairwise disjoint. (note that as a consequence
-- of currying and comutativity of products, this means that there are six
-- theorems to prove)
module progress-checks where
  -- boxed values and indeterminates are disjoint
  vi : ∀{d} → d boxedval → d indet → ⊥
  vi (BVVal VConst) ()
  vi (BVVal VLam) ()
  vi (BVArrCast x bv) (ICastArr x₁ ind) = vi bv ind
  vi (BVHoleCast x bv) (ICastGroundHole x₁ ind) = vi bv ind
  vi (BVHoleCast x bv) (ICastHoleGround x₁ ind x₂) = vi bv ind

  -- boxed values and errors are disjoint
  ve : ∀{d} → d boxedval → d casterr → ⊥
  ve (BVVal ()) (CECastFinal x₁ x₂ x₃ x₄)
  ve (BVHoleCast x bv) (CECastFinal x₁ x₂ () x₄)
  ve (BVArrCast x bv) (CECong FHOuter (CECong eps er)) = {!!}
  ve (BVArrCast x bv) (CECong (FHCast x₁) er) = ve bv (CECong x₁ er)
  ve (BVHoleCast x bv) (CECong x₁ er) = {!!}
  ve (BVVal x) (CECong x₁ er) = ve (lem-valfill x x₁) er
    where
    lem-valfill : ∀{ε d d'} → d val → d == ε ⟦ d' ⟧ → d' boxedval
    lem-valfill VConst FHOuter = BVVal VConst
    lem-valfill VLam FHOuter = BVVal VLam

  -- boxed values and expressions that step are disjoint
  vs : ∀{d} → d boxedval → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  vs (BVVal VConst) (d' , Step FHOuter () x₃)
  vs (BVVal VLam) (d' , Step FHOuter () x₃)
  vs (BVArrCast x bv) (d0' , Step FHOuter (ITCastID x₁) FHOuter) = x refl
  vs (BVArrCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = vs bv (_ , Step x₁ x₂ x₃)
  vs (BVHoleCast x bv) (d' , Step FHOuter x₂ FHOuter) = {!x₂!} -- cyrus
  vs (BVHoleCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = vs bv (_ , Step x₁ x₂ x₃)

  mutual
    -- indeterminates and errors are disjoint
    ie : ∀{d} → d indet → d casterr → ⊥
    ie IEHole (CECong FHOuter err) = ie IEHole err -- this is extremely strange
    ie (INEHole x) (CECong x₁ err) = {!!} -- fe x {!!}
    ie (IAp x indet x₁) (CECong x₂ err) = {!x₂!}
    ie (ICastArr x indet) (CECong x₁ err) = {!!}
    ie (ICastGroundHole x indet) (CECastFinal x₁ x₂ () x₄)
    ie (ICastGroundHole x indet) (CECong x₁ err) = {!!}
    ie (ICastHoleGround x indet x₁) (CECastFinal x₂ x₃ x₄ x₅) = {!!}
    ie (ICastHoleGround x indet x₁) (CECong x₂ err) = {!!}

    -- ie (INEHole x) (ENEHole e) = fe x e
    -- ie (IAp i x) (EAp1 e) = ie i e
    -- ie (IAp i x) (EAp2 y e) = fe x e
    -- ie (ICast i) (ECastError x x₁) = {!!} -- todo: this is evidence that casts are busted
    -- ie (ICast i) (ECastProp x) = ie i x

    -- final expressions are not errors (not one of the 6 cases for progress, just a convenience)
    fe : ∀{d} → d final → d casterr → ⊥
    fe (FBoxed x) err = ve x err
    fe (FIndet x) err = ie x err

  -- todo: these are bad names; probably some places below where i inlined
  -- some of these lemmas before i'd come up with them
  lem2 : ∀{d d'} → d indet → d →> d' → ⊥
  lem2 IEHole ()
  lem2 (INEHole x) ()
  lem2 (IAp x₁ () x₂) (ITLam x₃)
  lem2 (IAp x (ICastArr x₁ ind) x₂) (ITApCast x₃ x₄) = {!!} -- cyrus
  lem2 (ICastArr x ind) (ITCastID (FBoxed x₁)) = vi x₁ ind
  lem2 (ICastArr x ind) (ITCastID (FIndet x₁)) = x refl
  lem2 (ICastGroundHole x ind) stp = {!!}
  lem2 (ICastHoleGround x ind x₁) stp = {!!}

  lem3 : ∀{d d'} → d boxedval → d →> d' → ⊥
  lem3 (BVVal VConst) ()
  lem3 (BVVal VLam) ()
  lem3 (BVArrCast x bv) (ITCastID x₁) = x refl
  lem3 (BVHoleCast () bv) (ITCastID x₁)
  lem3 (BVHoleCast () bv) (ITCastSucceed x₁ x₂)
  lem3 (BVHoleCast GHole bv) (ITGround x₁) = {!!} -- cyrus

  lem1 : ∀{d d'} → d final → d →> d' → ⊥
  lem1 (FBoxed x) = lem3 x
  lem1 (FIndet x) = lem2 x

  lem4 : ∀{d ε x} → d final → d == ε ⟦ x ⟧ → x final
  lem4 (FBoxed x) FHOuter = FBoxed x
  lem4 (FBoxed (BVVal ())) (FHAp1 eps)
  lem4 (FBoxed (BVVal ())) (FHAp2 x₂ eps)
  lem4 (FBoxed (BVVal ())) (FHNEHole eps)
  lem4 (FBoxed (BVVal ())) (FHCast eps)
  lem4 (FBoxed (BVArrCast x₁ x₂)) (FHCast eps) = lem4 (FBoxed x₂) eps
  lem4 (FBoxed (BVHoleCast x₁ x₂)) (FHCast eps) = lem4 (FBoxed x₂) eps
  lem4 (FIndet x) FHOuter = FIndet x
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
    is : ∀{d} → d indet → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
    is IEHole (d' , Step FHOuter () FHOuter)
    is (INEHole x) (d' , Step FHOuter () FHOuter)
    is (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = lem5 x x₁ x₂
    is (IAp x₁ () x₂) (_ , Step FHOuter (ITLam x₃) FHOuter)
    is (IAp x (ICastArr x₁ ind) x₂) (_ , Step FHOuter (ITApCast x₃ x₄) FHOuter) = {!!} -- cyrus / maybe that error in the rule with pi-types
    is (IAp x ind _) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = is ind (_ , Step x₂ x₃ x₄)
    is (IAp x ind f) (_ , Step (FHAp2 x₂ x₃) x₄ (FHAp2 x₅ x₆)) = fs f (_ , Step x₃ x₄ x₆)
    is (ICastArr x ind) (d0' , Step FHOuter (ITCastID x₁) FHOuter) = x refl
    is (ICastArr x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = is ind (_ , Step x₁ x₂ x₃)
    is (ICastGroundHole () ind) (d' , Step FHOuter (ITCastID x₁) FHOuter)
    is (ICastGroundHole x ind) (d' , Step FHOuter (ITCastSucceed x₁ ()) FHOuter)
    is (ICastGroundHole GHole ind) (_ , Step FHOuter (ITGround (FBoxed x)) FHOuter) = vi x ind
    is (ICastGroundHole GHole ind) (_ , Step FHOuter (ITGround (FIndet x)) FHOuter) = {!!}
    is (ICastGroundHole x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = is ind (_ , Step x₁ x₂ x₃)
    is (ICastHoleGround x ind g) (d' , Step FHOuter x₂ FHOuter) = {!!}
    is (ICastHoleGround x ind g) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = is ind (_ , Step x₁ x₂ x₃)

    fs : ∀{d} → d final → Σ[ d' ∈ dhexp ] (d ↦ d') → ⊥
    fs (FBoxed x) stp = vs x stp
    fs (FIndet x) stp = is x stp

  -- errors and expressions that step are disjoint
  es : ∀{d} → d casterr → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  es er stp = {!!}
