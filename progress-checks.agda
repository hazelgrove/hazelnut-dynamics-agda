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
  vi : ∀{d} → d val → d indet → ⊥
  vi VConst ()
  vi VLam ()

  -- values and errors are disjoint
  ve : ∀{d Δ} → d val → Δ ⊢ d err → ⊥
  ve VConst ()
  ve VLam ()

  -- values and expressions that step are disjoint
  vs : ∀{d Δ} → d val → (Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d')) → ⊥
  vs VConst (_ , Step (FHFinal _) () _)
  vs VLam (_ , Step (FHFinal _) () _)

  mutual
    -- indeterminates and errors are disjoint
    ie : ∀{d Δ} → d indet → Δ ⊢ d err → ⊥
    ie IEHole ()
    ie (INEHole x) (ENEHole e) = fe x e
    ie (IAp i x) (EAp1 e) = ie i e
    ie (IAp i x) (EAp2 y e) = fe x e
    ie (ICast i) (ECastError x x₁) = {!!} -- todo: this is evidence that casts are busted
    ie (ICast i) (ECastProp x) = ie i x

    -- final expressions are not errors (not one of the 6 cases for progress, just a convenience)
    fe : ∀{d Δ} → d final → Δ ⊢ d err → ⊥
    fe (FVal x) er = ve x er
    fe (FIndet x) er = ie x er

  -- todo: these are bad names; probably some places below where i inlined
  -- some of these lemmas before i'd come up with them
  lem2 : ∀{d Δ d'} → d indet → Δ ⊢ d →> d' → ⊥
  lem2 IEHole ()
  lem2 (INEHole f) ()
  lem2 (IAp () _) (ITLam _)
  lem2 (ICast x) (ITCast (FVal x₁) x₂ x₃) = vi x₁ x
  lem2 (ICast x) (ITCast (FIndet x₁) x₂ x₃) = {!!} -- todo: this is evidence that casts are busted

  lem3 : ∀{d Δ d'} → d val → Δ ⊢ d →> d' → ⊥
  lem3 VConst ()
  lem3 VLam ()

  lem1 : ∀{d Δ d'} → d final → Δ ⊢ d →> d' → ⊥
  lem1 (FVal x) st = lem3 x st
  lem1 (FIndet x) st = lem2 x st

  lem4 : ∀{d ε x} → d final → d == ε ⟦ x ⟧ → x final
  lem4 f (FHFinal x) = x
  lem4 (FVal ()) (FHAp1 x₂ sub)
  lem4 (FIndet (IAp x₁ x₂)) (FHAp1 x₃ sub) = lem4 x₂ sub
  lem4 (FVal ()) (FHAp2 sub)
  lem4 (FIndet (IAp x₁ x₂)) (FHAp2 sub) = lem4 (FIndet x₁) sub
  lem4 f FHEHole = f
  lem4 f (FHNEHoleFinal x) = f
  lem4 (FVal ()) (FHCast sub)
  lem4 (FIndet (ICast i)) (FHCast sub) = lem4 (FIndet i) sub
  lem4 f (FHCastFinal x) = f
  lem4 (FVal ()) (FHNEHole y)
  lem4 (FIndet (INEHole x₁)) (FHNEHole y) = lem4 x₁ y

  lem5 : ∀{d Δ d' d'' ε} →  d final → d == ε ⟦ d' ⟧ → Δ ⊢ d' →> d'' → ⊥
  lem5 f sub step = lem1 (lem4 f sub) step

  -- indeterminates and expressions that step are disjoint
  is : ∀{d Δ} → d indet → (Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d')) → ⊥
  is IEHole (_ , Step (FHFinal x) q _) = lem1 x q
  is IEHole (_ , Step FHEHole () _)
  is (INEHole _) (_ , Step (FHFinal x₁) q _) = lem1 x₁ q
  is (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = lem5 x x₁ x₂
  is (INEHole x) (_ , Step (FHNEHoleFinal x₁) () FHEHole)
  is (INEHole x) (d , Step (FHNEHoleFinal x₁) () (FHFinal x₃))
  is (INEHole x) (_ , Step (FHNEHoleFinal x₁) () (FHNEHoleFinal x₃))
  is (INEHole x) (_ , Step (FHNEHoleFinal x₁) () (FHCastFinal x₃))
  is (IAp _ _) (_ , Step (FHFinal x₁) q _) = lem1 x₁ q
  is (IAp _ (FVal x)) (_ , Step (FHAp1 _ p) q (FHAp1 _ r)) = vs x (_ , Step p q r)
  is (IAp _ (FIndet x)) (_ , Step (FHAp1 _ p) q (FHAp1 _ r)) = is x (_ , Step p q r)
  is (IAp i x) (_ , Step (FHAp2 p) q (FHAp2 r)) = is i (_ , (Step p q r))
  is (ICast a) (d' , Step (FHFinal x) (ITCast x₁ x₂ x₃) x₄) = {!lem1 x₁!}
  is (ICast a) (_ , Step (FHCast x) x₁ (FHCast x₂)) = is a (_ , Step x x₁ x₂)
  is (ICast a) (d' , Step (FHCastFinal x) x₁ x₂) = {!x₂!}

  -- errors and expressions that step are disjoint
  es : ∀{d Δ} → Δ ⊢ d err → (Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d')) → ⊥
  -- cast error cases
  es (ECastError x x₁) (d' , Step (FHFinal x₂) x₃ x₄) = lem1 x₂ x₃
  es (ECastError x x₁) (_ , Step (FHCast x₂) x₃ (FHCast x₄)) = {!!}
  es (ECastError x x₁) (d' , Step (FHCastFinal x₂) (ITCast x₃ x₄ x₅) x₆)
    with type-assignment-unicity x x₄
  ... | refl = ~apart x₁ x₅

  -- ap1 cases
  es (EAp1 er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  es (EAp1 er) (_ , Step (FHAp1 x x₁) x₂ (FHAp1 x₃ x₄)) = fe x er
  es (EAp1 er) (_ , Step (FHAp2 x) x₁ (FHAp2 x₂)) = es er (_ , Step x x₁ x₂)

  -- ap2 cases
  es (EAp2 a er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  es (EAp2 a er) (_ , Step (FHAp1 x x₁) x₂ (FHAp1 x₃ x₄)) = es er (_ , Step x₁ x₂ x₄)
  es (EAp2 a er) (_ , Step (FHAp2 x) x₁ (FHAp2 x₂)) = lem5 a x x₁

  -- nehole cases
  es (ENEHole er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  es (ENEHole er) (_ , Step (FHNEHole a) x (FHNEHole x₂)) = es er (_ , Step a x x₂)
  es (ENEHole er) (d' , Step (FHNEHoleFinal x) x₁ x₂) = fe x er

  -- castprop cases
  es (ECastProp er) (d' , Step (FHFinal x) x₁ x₂) = lem1 x x₁
  es (ECastProp er) (_ , Step (FHCast x) x₁ (FHCast x₂)) = es er (_ , Step x x₁ x₂)
  es (ECastProp er) (d' , Step (FHCastFinal x) x₁ x₂) = fe x er
