open import Nat
open import Prelude
open import core
open import contexts
open import typed-expansion
open import lemmas-gcomplete
open import lemmas-complete

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
