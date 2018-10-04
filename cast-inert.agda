open import Nat
open import Prelude
open import core
open import contexts
open import typed-expansion
open import lemmas-gcomplete
open import lemmas-complete
open import progress-checks
open import finality

module cast-inert where
  -- if a term is compelete and well typed, then the casts inside are all
  -- identity casts and there are no failed casts
  cast-inert : ∀{Δ Γ d τ} →
                  Γ gcomplete →
                  d dcomplete →
                  Δ , Γ ⊢ d :: τ →
                  cast-id d
  cast-inert gc dc TAConst = CIConst
  cast-inert gc dc (TAVar x₁) = CIVar
  cast-inert gc (DCLam dc x₁) (TALam x₂ wt) = CILam (cast-inert (gcomp-extend gc x₁ x₂) dc wt)
  cast-inert gc (DCAp dc dc₁) (TAAp wt wt₁) = CIAp (cast-inert gc dc wt)
                                                   (cast-inert gc dc₁ wt₁)
  cast-inert gc () (TAEHole x x₁)
  cast-inert gc () (TANEHole x wt x₁)
  cast-inert gc (DCCast dc x x₁) (TACast wt x₂)
    with eq-complete-consist x x₁ x₂
  ... | refl = CICast (cast-inert gc dc wt)
  cast-inert gc () (TAFailedCast wt x x₁ x₂)

  -- relates expressions to the same thing with all identity casts removed
  data no-id-casts : dhexp → dhexp → Set where
    NICConst  : no-id-casts c c
    NICVar    : ∀{x} → no-id-casts (X x) (X x)
    NICLam    : ∀{x τ d d'} → no-id-casts d d' → no-id-casts (·λ x [ τ ] d) (·λ x [ τ ] d')
    NICHole   : ∀{u} → no-id-casts (⦇⦈⟨ u ⟩) (⦇⦈⟨ u ⟩)
    NICNEHole : ∀{d d' u} → no-id-casts d d' → no-id-casts (⦇ d ⦈⟨ u ⟩) (⦇ d' ⦈⟨ u ⟩)
    NICAp     : ∀{d1 d2 d1' d2'} → no-id-casts d1 d1' → no-id-casts d2 d2' → no-id-casts (d1 ∘ d2) (d1' ∘ d2')
    NICCast   : ∀{d d' τ} → no-id-casts d d' → no-id-casts (d ⟨ τ ⇒ τ ⟩) d'
    NICFailed : ∀{d d' τ1 τ2} → no-id-casts d d' → no-id-casts (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) (d' ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)

  -- removing identity casts doesn't change the type
  no-id-casts-type : ∀{Γ Δ d τ d' } → Δ , Γ ⊢ d :: τ → no-id-casts d d' → Δ , Γ ⊢ d' :: τ
  no-id-casts-type TAConst NICConst = TAConst
  no-id-casts-type (TAVar x₁) NICVar = TAVar x₁
  no-id-casts-type (TALam x₁ wt) (NICLam nic) = TALam x₁ (no-id-casts-type wt nic)
  no-id-casts-type (TAAp wt wt₁) (NICAp nic nic₁) = TAAp (no-id-casts-type wt nic) (no-id-casts-type wt₁ nic₁)
  no-id-casts-type (TAEHole x x₁) NICHole = TAEHole x x₁
  no-id-casts-type (TANEHole x wt x₁) (NICNEHole nic) = TANEHole x (no-id-casts-type wt nic) x₁
  no-id-casts-type (TACast wt x) (NICCast nic) = no-id-casts-type wt nic
  no-id-casts-type (TAFailedCast wt x x₁ x₂) (NICFailed nic) = TAFailedCast (no-id-casts-type wt nic) x x₁ x₂


  -- removing identity casts doesn't change the ultimate answer produced
  remove-casts-same : ∀{Δ d1 d2 d1' d2' Γ τ } →
                           Δ , Γ ⊢ d1 :: τ →
                           no-id-casts d1 d2 →
                           d1 ↦* d1' →
                           d2 ↦* d2' →
                           d1' final →
                           d2' final →
                           d1' == d2'
  remove-casts-same TAConst NICConst step1 step2 f1 f2 = ! (finality* (FBoxed (BVVal VConst)) step1) · finality* (FBoxed (BVVal VConst)) step2

  remove-casts-same (TAVar x₁) NICVar MSRefl step2 (FBoxed (BVVal ())) f2
  remove-casts-same (TAVar x₁) NICVar MSRefl step2 (FIndet ()) f2
  remove-casts-same (TAVar x₁) NICVar (MSStep (Step FHOuter () FHOuter) step1) step2 f1 f2

  remove-casts-same (TALam x₁ wt) (NICLam nic) MSRefl MSRefl (FBoxed (BVVal VLam)) (FBoxed (BVVal VLam)) = {!!} -- ap1 (λ qq → ·λ _ [ _ ] qq) {!!}
  remove-casts-same (TALam x₁ wt) (NICLam nic) MSRefl MSRefl _ (FIndet ())
  remove-casts-same (TALam x₁ wt) (NICLam nic) MSRefl MSRefl (FIndet ()) _
  remove-casts-same (TALam x₁ wt) (NICLam nic) MSRefl (MSStep x₂ step2) f1 f2 = abort (boxedval-not-step (BVVal VLam) ( _ , x₂))
  remove-casts-same (TALam x₁ wt) (NICLam nic) (MSStep x₂ step1) MSRefl f1 f2 = abort (boxedval-not-step (BVVal VLam) ( _ , x₂))
  remove-casts-same (TALam x₁ wt) (NICLam nic) (MSStep x₂ step1) (MSStep x₃ step2) f1 f2 = {!!}

  remove-casts-same (TAAp wt wt₁) (NICAp nic nic₁) MSRefl step2 (FBoxed (BVVal ())) f2
  remove-casts-same (TAAp wt wt₁) (NICAp nic nic₁) MSRefl step2 (FIndet (IAp x x₁ x₂)) f2 = {!!}
  remove-casts-same (TAAp wt wt₁) (NICAp nic nic₁) (MSStep x step1) step2 f1 f2 = {!!}

  remove-casts-same (TAEHole x x₁) NICHole MSRefl step2 (FBoxed (BVVal ())) f2
  remove-casts-same (TAEHole x x₁) NICHole MSRefl MSRefl (FIndet IEHole) (FBoxed (BVVal ()))
  remove-casts-same (TAEHole x x₁) NICHole MSRefl MSRefl (FIndet IEHole) (FIndet IEHole) = refl
  remove-casts-same (TAEHole x x₁) NICHole MSRefl (MSStep (Step FHOuter () FHOuter) step2) (FIndet IEHole) f2
  remove-casts-same (TAEHole x x₁) NICHole (MSStep (Step FHOuter () FHOuter) step1) step2 f1 f2

  remove-casts-same (TANEHole x wt x₁) (NICNEHole nic) step1 step2 f1 f2 = {!!}

  remove-casts-same (TACast wt x) (NICCast nic) MSRefl step2 (FBoxed (BVVal ())) f2
  remove-casts-same (TACast wt x) (NICCast nic) MSRefl step2 (FBoxed (BVArrCast x₁ x₂)) f2 = {!!}
  remove-casts-same (TACast wt x) (NICCast nic) MSRefl step2 (FBoxed (BVHoleCast () x₂)) f2
  remove-casts-same (TACast wt x) (NICCast nic) MSRefl step2 (FIndet (ICastArr x₁ x₂)) f2 = {!!}
  remove-casts-same (TACast wt x) (NICCast nic) MSRefl step2 (FIndet (ICastGroundHole () x₂)) f2
  remove-casts-same (TACast wt x) (NICCast nic) MSRefl step2 (FIndet (ICastHoleGround x₁ x₂ ())) f2
  remove-casts-same (TACast wt x) (NICCast nic) (MSStep x₁ step1) step2 f1 f2 = {!!}

  remove-casts-same (TAFailedCast wt x x₁ x₂) (NICFailed nic) step1 step2 f1 f2 = {!!}
