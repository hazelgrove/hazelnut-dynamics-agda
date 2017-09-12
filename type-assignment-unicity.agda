open import Nat
open import Prelude
open import List
open import core
open import contexts

module type-assignment-unicity where
  type-assignment-unicity : {Γ : tctx} {d : dhexp} {τ' τ : htyp} {Δ : hctx} →
                              Δ , Γ ⊢ d :: τ →
                              Δ , Γ ⊢ d :: τ' →
                              τ == τ'
  type-assignment-unicity TAConst TAConst = refl
  type-assignment-unicity {Γ = Γ} (TAVar x₁) (TAVar x₂) = ctxunicity {Γ = Γ} x₁ x₂
  type-assignment-unicity (TALam d1) (TALam d2)
    with type-assignment-unicity d1 d2
  ... | refl = refl
  type-assignment-unicity (TAAp d3 MAHole d4) (TAAp d5 MAHole d6) = refl
  type-assignment-unicity (TAAp d3 MAHole d4) (TAAp d5 MAArr d6)
      with type-assignment-unicity d3 d5
  ... | ()
  type-assignment-unicity (TAAp d3 MAArr d4) (TAAp d5 MAHole d6)
    with type-assignment-unicity d3 d5
  ... | ()
  type-assignment-unicity (TAAp d3 MAArr d4) (TAAp d5 MAArr d6)
    with type-assignment-unicity d3 d5 | type-assignment-unicity d4 d6
  ... | refl | refl = refl
  type-assignment-unicity (TAEHole {u = u} {Γ' = Γ'} {τ = τ} x) d2 = {!!}
  type-assignment-unicity (TANEHole d1 x) d2 = {!d2!}
  type-assignment-unicity (TACast d1 x) (TACast d2 x₁)
    with type-assignment-unicity d1 d2
  ... | refl = refl
