open import Nat
open import Prelude
open import core
open import contexts
open import typed-elaboration
open import lemmas-gcomplete
open import lemmas-complete
open import progress-checks
open import finality

module cast-inert where
  -- if a term is compelete and well typed, then the casts inside are all
  -- identity casts and there are no failed casts
  cast-inert : ∀{Δ Γ d τ} →
                  d dcomplete →
                  Δ , Γ ⊢ d :: τ →
                  cast-id d
  cast-inert dc TAConst = CIConst
  cast-inert dc (TAVar x₁) = CIVar
  cast-inert (DCLam dc x₁) (TALam x₂ wt) = CILam (cast-inert dc wt)
  cast-inert (DCAp dc dc₁) (TAAp wt wt₁) = CIAp (cast-inert dc wt) (cast-inert dc₁ wt₁)
  cast-inert () (TAEHole x x₁)
  cast-inert () (TANEHole x wt x₁)
  cast-inert (DCCast dc x x₁) (TACast wt x₂)
    with complete-consistency x₂ x x₁
  ... | refl = CICast (cast-inert dc wt)
  cast-inert () (TAFailedCast wt x x₁ x₂)

  -- in a well typed complete internal expression, every cast is the
  -- identity cast.
  complete-casts : ∀{Γ Δ d τ1 τ2} →
                   Γ , Δ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2 →
                   d ⟨ τ1 ⇒ τ2 ⟩ dcomplete →
                   τ1 == τ2
  complete-casts wt comp with cast-inert comp wt
  complete-casts wt comp | CICast qq = refl

  -- relates expressions to the same thing with all identity casts
  -- removed. note that this is a syntactic rewrite and it goes under
  -- binders.
  data no-id-casts : ihexp → ihexp → Set where
    NICConst  : no-id-casts c c
    NICVar    : ∀{x} → no-id-casts (X x) (X x)
    NICLam    : ∀{x τ d d'} → no-id-casts d d' → no-id-casts (·λ x [ τ ] d) (·λ x [ τ ] d')
    NICHole   : ∀{u} → no-id-casts (⦇⦈⟨ u ⟩) (⦇⦈⟨ u ⟩)
    NICNEHole : ∀{d d' u} → no-id-casts d d' → no-id-casts (⦇⌜ d ⌟⦈⟨ u ⟩) (⦇⌜ d' ⌟⦈⟨ u ⟩)
    NICAp     : ∀{d1 d2 d1' d2'} → no-id-casts d1 d1' → no-id-casts d2 d2' → no-id-casts (d1 ∘ d2) (d1' ∘ d2')
    NICCast   : ∀{d d' τ} → no-id-casts d d' → no-id-casts (d ⟨ τ ⇒ τ ⟩) d'
    NICFailed : ∀{d d' τ1 τ2} → no-id-casts d d' → no-id-casts (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) (d' ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)

  -- removing identity casts doesn't change the type
  no-id-casts-type : ∀{Γ Δ d τ d' } → Δ , Γ ⊢ d :: τ →
                                      no-id-casts d d' →
                                      Δ , Γ ⊢ d' :: τ
  no-id-casts-type TAConst NICConst = TAConst
  no-id-casts-type (TAVar x₁) NICVar = TAVar x₁
  no-id-casts-type (TALam x₁ wt) (NICLam nic) = TALam x₁ (no-id-casts-type wt nic)
  no-id-casts-type (TAAp wt wt₁) (NICAp nic nic₁) = TAAp (no-id-casts-type wt nic) (no-id-casts-type wt₁ nic₁)
  no-id-casts-type (TAEHole x x₁) NICHole = TAEHole x x₁
  no-id-casts-type (TANEHole x wt x₁) (NICNEHole nic) = TANEHole x (no-id-casts-type wt nic) x₁
  no-id-casts-type (TACast wt x) (NICCast nic) = no-id-casts-type wt nic
  no-id-casts-type (TAFailedCast wt x x₁ x₂) (NICFailed nic) = TAFailedCast (no-id-casts-type wt nic) x x₁ x₂
