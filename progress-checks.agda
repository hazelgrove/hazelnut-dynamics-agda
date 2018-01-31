open import Nat
open import Prelude
open import List
open import core
open import contexts
open import lemmas-consistency
open import canonical-forms
open import type-assignment-unicity

-- taken together, the theorems in this file argue that for any expression
-- d, at most one summand of the labeled sum that results from progress may
-- be true at any time, i.e. that values, indeterminates, errors, and
-- expressions that step are pairwise disjoint. (note that as a consequence
-- of currying and comutativity of products, this means that there are six
-- theorems to prove)
module progress-checks where
  -- values and indeterminates are disjoint
  vi : ∀{d} → d boxedval → d indet → ⊥
  vi (BVVal VConst) ()
  vi (BVVal VLam) ()
  vi (BVArrCast x bv) (ICastArr x₁ ind) = vi bv ind
  vi (BVHoleCast x bv) (ICastGroundHole x₁ ind) = vi bv ind
  vi (BVHoleCast x bv) (ICastHoleGround x₁ ind x₂) = vi bv ind

  lem-valfill : ∀{ε d d'} → d val → d == ε ⟦ d' ⟧ → d' val
  lem-valfill VConst FHOuter = VConst
  lem-valfill VLam FHOuter = VLam

  -- values and errors are disjoint
  ve : ∀{d} → d boxedval → d casterr → ⊥
  ve (BVVal ()) (CECastFinal x₁ x₂ x₃ x₄)
  ve (BVHoleCast x bv) (CECastFinal x₁ x₂ () x₄)
  ve (BVVal x) (CECong x₁ er) = ve (BVVal (lem-valfill x x₁)) er
  ve (BVArrCast x bv) (CECong FHOuter (CECong x₁ er)) = {!!} -- ve bv {!!}
  ve (BVArrCast x bv) (CECong (FHCast x₁) er) = ve bv (CECong x₁ er)
  ve (BVHoleCast x bv) (CECong x₁ er) = {!!}

  -- values and expressions that step are disjoint
  vs : ∀{d} → d boxedval → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  vs (BVVal VConst) (d' , Step FHOuter () x₃)
  vs (BVVal VLam) (d' , Step FHOuter () x₃)
  vs (BVArrCast x bv) (d' , Step x₁ x₂ x₃) = {!x₂!}
  vs (BVHoleCast x bv) s = {!!}

  mutual
    -- indeterminates and errors are disjoint
    ie : ∀{d} → d indet → d casterr → ⊥
    ie IEHole err = {!err!}
    ie (INEHole x) err = {!!}
    ie (IAp x indet x₁) err = {!!}
    ie (ICastArr x indet) err = {!!}
    ie (ICastGroundHole x indet) err = {!!}
    ie (ICastHoleGround x indet x₁) err = {!!}
    -- ie IEHole ()
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
  lem2 (ICastArr x ind) (ITCastID (FIndet x₁)) = {!!} -- cyrus
  lem2 (ICastGroundHole x ind) stp = {!!}
  lem2 (ICastHoleGround x ind x₁) stp = {!!}

  lem3 : ∀{d d'} → d boxedval → d →> d' → ⊥ -- boxed?
  lem3 (BVVal VConst) ()
  lem3 (BVVal VLam) ()
  lem3 (BVArrCast x bv) st = {!!}
  lem3 (BVHoleCast x bv) st = {!!}

  lem1 : ∀{d d'} → d final → d →> d' → ⊥
  lem1 (FBoxed x) = lem3 x
  lem1 (FIndet x) = lem2 x

  lem1' : ∀{d d'} → d final → d ↦ d' → ⊥
  lem1' fin = {!!}

  -- lem1 (FVal x) st = lem3 x st
  -- lem1 (FIndet x) st = lem2 x st

  lem4 : ∀{d ε x} → d final → d == ε ⟦ x ⟧ → x final
  lem4 = {!!}
  -- lem4 f (FHFinal x) = x
  -- lem4 (FVal ()) (FHAp1 x₂ sub)
  -- lem4 (FIndet (IAp x₁ x₂)) (FHAp1 x₃ sub) = lem4 x₂ sub
  -- lem4 (FVal ()) (FHAp2 sub)
  -- lem4 (FIndet (IAp x₁ x₂)) (FHAp2 sub) = lem4 (FIndet x₁) sub
  -- lem4 f FHEHole = f
  -- lem4 f (FHNEHoleFinal x) = f
  -- lem4 (FVal ()) (FHCast sub)
  -- lem4 (FIndet (ICast i)) (FHCast sub) = lem4 (FIndet i) sub
  -- lem4 f (FHCastFinal x) = f
  -- lem4 (FVal ()) (FHNEHole y)
  -- lem4 (FIndet (INEHole x₁)) (FHNEHole y) = lem4 x₁ y

  lem5 : ∀{d d' d'' ε} →  d final → d == ε ⟦ d' ⟧ → d' →> d'' → ⊥
  lem5 f sub step = lem1 (lem4 f sub) step



  -- indeterminates and expressions that step are disjoint
  is : ∀{d} → d indet → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  is IEHole (d' , Step FHOuter () FHOuter)
  is (INEHole x) (d' , Step FHOuter () FHOuter)
  is (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = lem5 x x₁ x₂
  is (IAp x₁ () x₂) (_ , Step FHOuter (ITLam x₃) FHOuter)
  is (IAp x (ICastArr x₁ ind) x₂) (_ , Step FHOuter (ITApCast x₃ x₄) FHOuter) = {!!}
  is (IAp x ind x₁) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = is ind (_ , Step x₂ x₃ x₄)
  is (IAp x ind x₁) (_ , Step (FHAp2 x₂ x₃) x₄ (FHAp2 x₅ x₆)) = lem1 x₁ {!π2 (lem6 (Step x₃ x₄ x₆))!}
  is (ICastArr x ind) stp = {!!}
  is (ICastGroundHole x ind) stp = {!!}
  is (ICastHoleGround x ind g) stp = {!!}
  -- is (IAp _ _) (_ , Step (FHFinal x₁) q _) = lem1 x₁ q
  -- is (IAp _ (FVal x)) (_ , Step (FHAp1 _ p) q (FHAp1 _ r)) = vs x (_ , Step p q r)
  -- is (IAp _ (FIndet x)) (_ , Step (FHAp1 _ p) q (FHAp1 _ r)) = is x (_ , Step p q r)
  -- is (IAp i x) (_ , Step (FHAp2 p) q (FHAp2 r)) = is i (_ , (Step p q r))
  -- is (ICast a) (d' , Step (FHFinal x) q x₄) = lem1 x q
  -- is (ICast a) (_ , Step (FHCast x) x₁ (FHCast x₂)) = is a (_ , Step x x₁ x₂)
  -- is (ICast a) (d' , Step (FHCastFinal x) x₁ x₂) = lem5 (FIndet (ICast a)) (FHCastFinal x) x₁ -- todo: this feels odd

  -- errors and expressions that step are disjoint
  es : ∀{d} → d casterr → (Σ[ d' ∈ dhexp ] (d ↦ d')) → ⊥
  es er stp = {!e!}
  -- -- cast error cases
  -- es (ECastError x x₁) (d' , Step (FHFinal x₂) x₃ x₄) = lem1 x₂ x₃
  -- es (ECastError x x₁) (_ , Step (FHCast x₂) x₃ (FHCast x₄)) = {!!} -- todo: this is evidence that casts are busted
  -- es (ECastError x x₁) (d' , Step (FHCastFinal x₂) (ITCast x₃ x₄ x₅) x₆)
  --   with type-assignment-unicity x x₄
  -- ... | refl = ~apart x₁ x₅

  -- -- ap1 cases
  -- es (EAp1 er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  -- es (EAp1 er) (_ , Step (FHAp1 x x₁) x₂ (FHAp1 x₃ x₄)) = fe x er
  -- es (EAp1 er) (_ , Step (FHAp2 x) x₁ (FHAp2 x₂)) = es er (_ , Step x x₁ x₂)

  -- -- ap2 cases
  -- es (EAp2 a er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  -- es (EAp2 a er) (_ , Step (FHAp1 x x₁) x₂ (FHAp1 x₃ x₄)) = es er (_ , Step x₁ x₂ x₄)
  -- es (EAp2 a er) (_ , Step (FHAp2 x) x₁ (FHAp2 x₂)) = lem5 a x x₁

  -- -- nehole cases
  -- es (ENEHole er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  -- es (ENEHole er) (_ , Step (FHNEHole a) x (FHNEHole x₂)) = es er (_ , Step a x x₂)
  -- es (ENEHole er) (d' , Step (FHNEHoleFinal x) x₁ x₂) = fe x er

  -- -- castprop cases
  -- es (ECastProp er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  -- es (ECastProp er) (_ , Step (FHCast x) x₁ (FHCast x₂)) = es er (_ , Step x x₁ x₂)
  -- es (ECastProp er) (d' , Step (FHCastFinal x) x₁ x₂) = fe x er
