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
                  τ tcomplete →
                  Δ , Γ ⊢ d :: τ →
                  cast-id d
  cast-inert gc dc tc TAConst = CIConst
  cast-inert gc dc tc (TAVar x₁) = CIVar
  cast-inert gc (DCLam dc x₁) (TCArr tc tc₁) (TALam x₂ wt) = CILam (cast-inert (gcomp-extend gc x₁ x₂) dc tc₁ wt)
  cast-inert gc (DCAp dc dc₁) TCBase (TAAp wt wt₁)
    with complete-ta gc wt₁ dc₁
  ... | cτ = CIAp (cast-inert gc dc (TCArr cτ TCBase) wt)
                  (cast-inert gc dc₁ cτ wt₁)
  cast-inert gc (DCAp dc dc₁) (TCArr tc tc₁) (TAAp wt wt₁)
    with (complete-ta gc wt₁ dc₁)
  ... | cτ3 = CIAp (cast-inert gc dc (TCArr cτ3 (TCArr tc tc₁)) wt)
                   (cast-inert gc dc₁ cτ3 wt₁)
  cast-inert gc () tc (TAEHole x x₁)
  cast-inert gc () tc (TANEHole x wt x₁)
  cast-inert gc (DCCast dc x x₁) tc (TACast wt x₂)
    with eq-complete-consist x x₁ x₂
  ... | refl = CICast (cast-inert gc dc tc wt)
  cast-inert gc () tc (TAFailedCast wt x x₁ x₂)
