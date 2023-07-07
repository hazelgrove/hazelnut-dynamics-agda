open import Nat
open import Prelude
open import core
open import contexts

module type-assignment-unicity where
  open typctx

  -- type assignment only assigns one type
  type-assignment-unicity : {Γ : tctx} {d : ihexp} {τ' τ : htyp} {Δ : hctx} {Θ : typctx} →
                              Δ , Γ , Θ ⊢ d :: τ →
                              Δ , Γ , Θ ⊢ d :: τ' →
                              τ == τ'
  type-assignment-unicity TAConst TAConst = refl
  type-assignment-unicity {Γ = Γ} (TAVar x₁) (TAVar x₂) = ctxunicity {Γ = Γ} x₁ x₂
  type-assignment-unicity (TALam _ d1) (TALam _ d2)
    with type-assignment-unicity d1 d2
  ... | refl = refl
  type-assignment-unicity (TATLam d1) (TATLam d2)
    with type-assignment-unicity d1 d2
  ... | refl = refl
  type-assignment-unicity (TAAp x x₁) (TAAp y y₁)
    with type-assignment-unicity x y
  ... | refl = refl
  type-assignment-unicity (TATAp x) (TATAp y)
    with type-assignment-unicity x y
  ... | refl = refl
  type-assignment-unicity (TAEHole {Δ = Δ} x y) (TAEHole x₁ x₂)
    with ctxunicity {Γ = Δ} x x₁
  ... | refl = refl
  type-assignment-unicity (TANEHole {Δ = Δ} x d1 y) (TANEHole x₁ d2 x₂)
    with ctxunicity {Γ = Δ} x₁ x
  ... | refl = refl
  type-assignment-unicity (TACast d1 x) (TACast d2 x₁)
    with type-assignment-unicity d1 d2
  ... | refl = refl
  type-assignment-unicity (TAFailedCast x x₁ x₂ x₃) (TAFailedCast y x₄ x₅ x₆)
    with type-assignment-unicity x y
  ... | refl = refl
