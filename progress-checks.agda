open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency
open import type-assignment-unicity

-- taken together, the theorems in this file argue that for any expression
-- d, at most one summand of the labeled sum that results from progress may
-- be true at any time, i.e. that boxed values, indeterminates, cast
-- errors, and expressions that step are pairwise disjoint. (note that as a
-- consequence of currying and comutativity of products, this means that
-- there are six theorems to prove)
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
  ve (BVVal ()) (CECastFail x₁ x₂ x₃ x₄)
  ve (BVHoleCast x bv) (CECastFail x₁ x₂ () x₄)
  ve (BVArrCast x bv) (CECong FHOuter er) = ve bv (lem er)
    where
    -- todo: also being used below
    lem : ∀{d τ1 τ2 τ3 τ4} → (d ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩) casterr → d casterr
    lem (CECong FHOuter ce) = lem ce
    lem (CECong (FHCast x₁) ce) = CECong x₁ ce
  ve (BVArrCast x bv) (CECong (FHCast x₁) er) = ve bv (CECong x₁ er)
  ve (BVHoleCast x bv) (CECong FHOuter er) = ve bv (lem er)
    where
    --- todo: okay this is now getting reused here and in the case of ie
    --- below, so this is apparently more of an interesting property than
    --- i'd thought
    lem : ∀{d τ} → (d ⟨ τ ⇒ ⦇⦈ ⟩) casterr → d casterr
    lem (CECastFail x₁ x₂ () x₄)
    lem (CECong FHOuter ce) = lem ce
    lem (CECong (FHCast x₁) ce) = CECong x₁ ce
  ve (BVHoleCast x bv) (CECong (FHCast x₁) er) = ve bv (CECong x₁ er)
  ve (BVVal x) (CECong FHOuter er) = ve (BVVal x) er
  ve (BVVal ()) (CECong (FHAp1 x₁) er)
  ve (BVVal ()) (CECong (FHAp2 x₁ x₂) er)
  ve (BVVal ()) (CECong (FHNEHole x₁) er)
  ve (BVVal ()) (CECong (FHCast x₁) er)

  -- boxed values and expressions that step are disjoint
  vs : ∀{d} → d boxedval → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  vs (BVVal VConst) (d' , Step FHOuter () x₃)
  vs (BVVal VLam) (d' , Step FHOuter () x₃)
  vs (BVArrCast x bv) (d0' , Step FHOuter (ITCastID x₁) FHOuter) = x refl
  vs (BVArrCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = vs bv (_ , Step x₁ x₂ x₃)
  vs (BVHoleCast () bv) (d' , Step FHOuter (ITCastID x₁) FHOuter)
  vs (BVHoleCast x bv) (d' , Step FHOuter (ITCastSucceed x₁ ()) FHOuter)
  vs (BVHoleCast GHole bv) (_ , Step FHOuter (ITGround x₁ x₂) FHOuter) = x₂ refl
  vs (BVHoleCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = vs bv (_ , Step x₁ x₂ x₃)

  -- todo: what class of P is this true for?
  -- lem-something : ∀{ d ε d'} → d == ε ⟦ d' ⟧ → P d' → P d

  mutual
    -- todo: there's something going on with these lemmas here that's
    -- repetative and i don't quite understand how to make it more compact

    -- indeterminates and errors are disjoint
    ie : ∀{d} → d indet → d casterr → ⊥
    ie IEHole (CECong FHOuter err) = ie IEHole err
    ie (INEHole x) (CECong FHOuter err) = fe x (lem err)
      where
      lem : ∀{d u σ} → ⦇ d ⦈⟨ u , σ ⟩ casterr → d casterr
      lem (CECong FHOuter ce) = lem ce
      lem (CECong (FHNEHole x₁) ce) = CECong x₁ ce
    ie (INEHole x) (CECong (FHNEHole x₁) err) = fe x (CECong x₁ err)
    ie (IAp x indet x₁) (CECong FHOuter err)
      with lem err
      where
      lem : ∀{d1 d2} → (d1 ∘ d2) casterr → (d1 casterr + d2 casterr)
      lem (CECong FHOuter ce) = lem ce
      lem (CECong (FHAp1 x₂) ce) = Inl (CECong x₂ ce)
      lem (CECong (FHAp2 x₂ x₃) ce) = Inr (CECong x₃ ce)
    ... | Inl d1err = ie indet d1err
    ... | Inr d2err = fe x₁ d2err
      where
    ie (IAp x indet x₁) (CECong (FHAp1 x₂) err) = ie indet (CECong x₂ err)
    ie (IAp x indet x₁) (CECong (FHAp2 x₂ x₃) err) = fe x₁ (CECong x₃ err)
    ie (ICastArr x indet) (CECong FHOuter err) = ie indet (lem err)
      where
      lem : ∀{d τ1 τ2 τ3 τ4} → (d ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩) casterr → d casterr
      lem (CECong FHOuter ce) = lem ce
      lem (CECong (FHCast x₁) ce) = CECong x₁ ce
    ie (ICastArr x indet) (CECong (FHCast x₁) err) = ie indet (CECong x₁ err)
    ie (ICastGroundHole x indet) (CECastFail x₁ x₂ () x₄)
    ie (ICastGroundHole x indet) (CECong FHOuter err) = ie indet (lem err)
      where
      lem : ∀{d τ} → (d ⟨ τ ⇒ ⦇⦈ ⟩) casterr → d casterr
      lem (CECastFail x₁ x₂ () x₄)
      lem (CECong FHOuter ce) = lem ce
      lem (CECong (FHCast x₁) ce) = CECong x₁ ce
    ie (ICastGroundHole x indet) (CECong (FHCast x₁) err) = ie indet (CECong x₁ err)
    ie (ICastHoleGround x indet x₁) (CECastFail x₂ x₃ x₄ x₅) = x _ _ refl
    ie (ICastHoleGround x indet x₁) (CECong FHOuter err) = ie indet (lem err x)
      where
      lem : ∀{d τ} → (d ⟨ ⦇⦈ ⇒ τ ⟩) casterr → ((d' : dhexp) (τ' : htyp) → d ≠ (d' ⟨ τ' ⇒ ⦇⦈ ⟩)) → d casterr
      lem (CECastFail x₂ x₃ x₄ x₅) f = abort (f _ _ refl)
      lem (CECong FHOuter ce) = lem ce
      lem (CECong (FHCast x₂) ce) _ = CECong x₂ ce
    ie (ICastHoleGround x indet x₁) (CECong (FHCast x₂) err) = ie indet (CECong x₂ err)

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
  lem2 (IAp x (ICastArr x₁ ind) x₂) (ITApCast x₃ x₄) = x _ _ _ _ _ refl
  lem2 (ICastArr x ind) (ITCastID (FBoxed x₁)) = vi x₁ ind
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
    is : ∀{d} → d indet → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
    is IEHole (d' , Step FHOuter () FHOuter)
    is (INEHole x) (d' , Step FHOuter () FHOuter)
    is (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = lem5 x x₁ x₂
    is (IAp x₁ () x₂) (_ , Step FHOuter (ITLam x₃) FHOuter)
    is (IAp x (ICastArr x₁ ind) x₂) (_ , Step FHOuter (ITApCast x₃ x₄) FHOuter) = x _ _ _ _ _  refl
    is (IAp x ind _) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = is ind (_ , Step x₂ x₃ x₄)
    is (IAp x ind f) (_ , Step (FHAp2 x₂ x₃) x₄ (FHAp2 x₅ x₆)) = fs f (_ , Step x₃ x₄ x₆)
    is (ICastArr x ind) (d0' , Step FHOuter (ITCastID x₁) FHOuter) = x refl
    is (ICastArr x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = is ind (_ , Step x₁ x₂ x₃)
    is (ICastGroundHole () ind) (d' , Step FHOuter (ITCastID x₁) FHOuter)
    is (ICastGroundHole x ind) (d' , Step FHOuter (ITCastSucceed x₁ ()) FHOuter)
    is (ICastGroundHole GHole ind) (_ , Step FHOuter (ITGround _ y) FHOuter) = y refl
    is (ICastGroundHole x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = is ind (_ , Step x₁ x₂ x₃)
    is (ICastHoleGround x ind ()) (d' , Step FHOuter (ITCastID x₁) FHOuter)
    is (ICastHoleGround x ind g) (d' , Step FHOuter (ITCastSucceed x₁ x₂) FHOuter) = x _ _ refl
    is (ICastHoleGround x ind GHole) (_ , Step FHOuter (ITExpand x₁ x₂) FHOuter) = x₂ refl
    is (ICastHoleGround x ind g) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = is ind (_ , Step x₁ x₂ x₃)

    fs : ∀{d} → d final → Σ[ d' ∈ dhexp ] (d ↦ d') → ⊥
    fs (FBoxed x) stp = vs x stp
    fs (FIndet x) stp = is x stp

  -- errors and expressions that step are disjoint
  es : ∀{d} → d casterr → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  es (CECastFail x x₁ () x₃) (_ , Step FHOuter (ITCastID x₄) FHOuter)
  es (CECastFail x x₁ x₂ x₃) (d' , Step FHOuter (ITCastSucceed x₄ x₅) FHOuter) = x₃ refl
  es (CECastFail x x₁ GHole x₃) (_ , Step FHOuter (ITExpand x₄ x₅) FHOuter) = x₅ refl
  es (CECastFail x x₁ x₂ x₃) (_ , Step (FHCast x₄) x₅ (FHCast x₆)) = {!!} -- cyrus

  es (CECong FHOuter er) (d0' , Step FHOuter x₂ FHOuter) = es er (_ , Step FHOuter x₂ FHOuter)
  es (CECong (FHAp1 x) er) (d0' , Step FHOuter x₂ FHOuter) = {!er!}
  es (CECong (FHAp2 x x₁) er) (d0' , Step FHOuter x₂ FHOuter) = {!!}
  es (CECong (FHNEHole x) er) (d0' , Step FHOuter x₂ FHOuter) = {!!}
  es (CECong (FHCast x) er) (d0' , Step FHOuter x₂ FHOuter) = {!!}

  es (CECong FHOuter er) (_ , Step (FHAp1 x₁) x₂ (FHAp1 x₃)) = {!!}
  es (CECong (FHAp1 x) er) (_ , Step (FHAp1 x₁) x₂ (FHAp1 x₃)) = {!!}
  es (CECong (FHAp2 x x₁) er) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = fs x (_ , Step x₂ x₃ x₄)

  es (CECong FHOuter er) (_ , Step (FHAp2 x₁ x₂) x₃ (FHAp2 x₄ x₅)) = {!!}
  es (CECong (FHAp1 x) er) (_ , Step (FHAp2 x₁ x₂) x₃ (FHAp2 x₄ x₅)) = {!!}
  es (CECong (FHAp2 x x₁) er) (_ , Step (FHAp2 x₂ x₃) x₄ (FHAp2 x₅ x₆)) = {!!}
  --     with lem {!!}
  --     where
  --     lem : ∀{d1 d2} → (d1 ∘ d2) casterr → (d1 casterr + d2 casterr)
  --     lem (CECong FHOuter ce) = lem ce
  --     lem (CECong (FHAp1 x₂) ce) = Inl (CECong x₂ ce)
  --     lem (CECong (FHAp2 x₂ x₃) ce) = Inr (CECong x₃ ce)
  -- ... | Inl d1err = {!!}
  -- ... | Inr d2err = {!!} -- = es {!!} (_ , Step x₂ x₃ x₅)
  es (CECong FHOuter er) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = {!!}
  es (CECong (FHNEHole x) er) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = {!!}

  es (CECong FHOuter er) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = {!!}
  es (CECong (FHCast x) er) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = {!!}
