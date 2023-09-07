open import Nat
open import Prelude
open import core
open import contexts

module type-assignment-unicity where

  -- type assignment only assigns one type
  type-assignment-unicity : {Γ : tctx} {d : ihexp} {τ' τ : htyp} {Δ : hctx} {Θ : typctx} →
                              Δ , Θ , Γ ⊢ d :: τ →
                              Δ , Θ , Γ ⊢ d :: τ' →
                              τ == τ'
  type-assignment-unicity TAConst TAConst = refl
  type-assignment-unicity {Γ = Γ} (TAVar x₁) (TAVar x₂) = ctxunicity {Γ = Γ} x₁ x₂
  type-assignment-unicity (TALam _ _ d1) (TALam _ _ d2)
    with type-assignment-unicity d1 d2
  ... | refl = refl
  type-assignment-unicity (TATLam apt1 d1) (TATLam apt2 d2)
    with type-assignment-unicity d1 d2
  ... | refl = refl
  type-assignment-unicity (TAAp x x₁ xalpha) (TAAp y y₁ yalpha)
    with type-assignment-unicity x y
  ... | refl = refl
  type-assignment-unicity (TATAp _ x eq1) (TATAp _ y eq2) with type-assignment-unicity x y
  ... | refl rewrite eq1 = eq2
  type-assignment-unicity (TAEHole {Δ = Δ} x y eq1 _) (TAEHole x₁ x₂ eq2 _)
    with ctxunicity {Γ = Δ} x x₁
  ... | refl rewrite eq1 | eq2 = refl
  type-assignment-unicity (TANEHole {Δ = Δ} x d1 y eq1 _) (TANEHole x₁ d2 x₂ eq2 _)
    with ctxunicity {Γ = Δ} x₁ x
  ... | refl rewrite eq1 | eq2 = refl
  type-assignment-unicity (TACast d1 _ x alpha1) (TACast d2 _ x₁ alpha2)
    with type-assignment-unicity d1 d2
  ... | refl = refl
  type-assignment-unicity (TAFailedCast x x₁ x₂ x₃ _) (TAFailedCast y x₄ x₅ x₆ _)
    with type-assignment-unicity x y
  ... | refl = refl
