open import Nat
open import Prelude
open import List
open import core

module lemmas-progress-checks where
  boxedval-not-trans : ∀{d d'} → d boxedval → d →> d' → ⊥
  boxedval-not-trans (BVVal VConst) ()
  boxedval-not-trans (BVVal VLam) ()
  boxedval-not-trans (BVArrCast x bv) (ITCastID x₁) = x refl
  boxedval-not-trans (BVHoleCast () bv) (ITCastID x₁)
  boxedval-not-trans (BVHoleCast () bv) (ITCastSucceed x₁ x₂)
  boxedval-not-trans (BVHoleCast GHole bv) (ITGround x₁ (MGArr x)) = x refl
  boxedval-not-trans (BVHoleCast x a) (ITExpand x₁ ())

  indet-not-trans : ∀{d d'} → d indet → d →> d' → ⊥
  indet-not-trans IEHole ()
  indet-not-trans (INEHole x) ()
  indet-not-trans (IAp x₁ () x₂) (ITLam x₃)
  indet-not-trans (IAp x (ICastArr x₁ ind) x₂) (ITApCast x₃ x₄) = x _ _ _ _ _ refl
  indet-not-trans (ICastArr x ind) (ITCastID _) = x refl
  indet-not-trans (ICastGroundHole () ind) (ITCastID x₁)
  indet-not-trans (ICastGroundHole x ind) (ITCastSucceed x₁ ())
  indet-not-trans (ICastGroundHole GHole ind) (ITGround x₁ (MGArr x)) = x refl
  indet-not-trans (ICastHoleGround x ind ()) (ITCastID x₂)
  indet-not-trans (ICastHoleGround x ind x₁) (ITCastSucceed x₂ x₃) = x _ _ refl
  indet-not-trans (ICastHoleGround x ind GHole) (ITExpand (FBoxed x₁) (MGArr x₂)) = x₂ refl
  indet-not-trans (ICastGroundHole x a) (ITExpand x₁ ())
  indet-not-trans (ICastHoleGround x a x₁) (ITGround x₂ ())
  indet-not-trans (ICastHoleGround x a GHole) (ITExpand x₂ (MGArr x₃)) = x₃ refl

  final-not-trans : ∀{d d'} → d final → d →> d' → ⊥
  final-not-trans (FBoxed x) = boxedval-not-trans x
  final-not-trans (FIndet x) = indet-not-trans x

  final-sub-final : ∀{d ε x} → d final → d == ε ⟦ x ⟧ → x final
  final-sub-final x FHOuter = x
  final-sub-final (FBoxed (BVVal ())) (FHAp1 eps)
  final-sub-final (FBoxed (BVVal ())) (FHAp2 x₂ eps)
  final-sub-final (FBoxed (BVVal ())) (FHNEHole eps)
  final-sub-final (FBoxed (BVVal ())) (FHCast eps)
  final-sub-final (FBoxed (BVArrCast x₁ x₂)) (FHCast eps) = final-sub-final (FBoxed x₂) eps
  final-sub-final (FBoxed (BVHoleCast x₁ x₂)) (FHCast eps) = final-sub-final (FBoxed x₂) eps
  final-sub-final (FIndet (IAp x₁ x₂ x₃)) (FHAp1 eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (IAp x₁ x₂ x₃)) (FHAp2 x₄ eps) = final-sub-final x₃ eps
  final-sub-final (FIndet (INEHole x₁)) (FHNEHole eps) = final-sub-final x₁ eps
  final-sub-final (FIndet (ICastArr x₁ x₂)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (ICastGroundHole x₁ x₂)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (ICastHoleGround x₁ x₂ x₃)) (FHCast eps) = final-sub-final (FIndet x₂) eps

  final-sub-not-trans : ∀{d d' d'' ε} →  d final → d == ε ⟦ d' ⟧ → d' →> d'' → ⊥
  final-sub-not-trans f sub step = final-not-trans (final-sub-final f sub) step

  ce-castarr : ∀{d τ1 τ2 τ3 τ4} → (d ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩) casterr → d casterr
  ce-castarr (CECong FHOuter ce) = ce-castarr ce
  ce-castarr (CECong (FHCast x₁) ce) = CECong x₁ ce

  ce-castth : ∀{d τ} → (d ⟨ τ ⇒ ⦇⦈ ⟩) casterr → d casterr
  ce-castth (CECastFail x₁ x₂ () x₄)
  ce-castth (CECong FHOuter ce) = ce-castth ce
  ce-castth (CECong (FHCast x₁) ce) = CECong x₁ ce

  ce-nehole : ∀{d u σ} → ⦇ d ⦈⟨ u , σ ⟩ casterr → d casterr
  ce-nehole (CECong FHOuter ce) = ce-nehole ce
  ce-nehole (CECong (FHNEHole x₁) ce) = CECong x₁ ce

  ce-ap : ∀{d1 d2} → (d1 ∘ d2) casterr → (d1 casterr + d2 casterr)
  ce-ap (CECong FHOuter ce) = ce-ap ce
  ce-ap (CECong (FHAp1 x₂) ce) = Inl (CECong x₂ ce)
  ce-ap (CECong (FHAp2 x₂ x₃) ce) = Inr (CECong x₃ ce)

  ce-castht : ∀{d τ} → (d ⟨ ⦇⦈ ⇒ τ ⟩) casterr → ((d' : dhexp) (τ' : htyp) → d ≠ (d' ⟨ τ' ⇒ ⦇⦈ ⟩)) → d casterr
  ce-castht (CECastFail x₂ x₃ x₄ x₅) f = abort (f _ _ refl)
  ce-castht (CECong FHOuter ce) = ce-castht ce
  ce-castht (CECong (FHCast x₂) ce) _ = CECong x₂ ce

  ce-out-cast : ∀{d d' ε} →
                d casterr →
                d' == ε ⟦ d ⟧ →
                d' casterr
  ce-out-cast (CECong x ce) FHOuter = ce-out-cast ce x
  ce-out-cast (CECong x ce) y = CECong y (ce-out-cast ce x)
  ce-out-cast z FHOuter = z
  ce-out-cast z y = CECong y z
