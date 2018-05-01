open import Nat
open import Prelude
open import core
open import contexts

module instantiation where
  instantiation : ∀{Δ Γ d τ u Γ' τ' d'} →
                      Δ , Γ ⊢ d :: τ →
                      (u ::[ Γ' ] τ') ∈ Δ →
                      Δ , Γ ⊢ d' :: τ' →
                      Δ , Γ ⊢ ⟦ d' / u ⟧ d :: τ
  instantiation TAConst cont wt2 = TAConst
  instantiation (TAVar x₁) cont wt2 = TAVar x₁
  instantiation (TALam apt wt1) cont wt2 = TALam apt {!!}
  instantiation (TAAp wt1 wt2) cont wt3 = TAAp (instantiation wt1 cont wt3)
                                               (instantiation wt2 cont wt3)
  instantiation (TAEHole x x₁) cont wt2 = {!!}
  instantiation (TANEHole x wt1 x₁) cont wt2 = {!!}
  instantiation (TACast wt1 x) cont wt2 = TACast (instantiation wt1 cont wt2) x
  instantiation (TAFailedCast wt1 x x₁ x₂) cont wt2 = TAFailedCast (instantiation wt1 cont wt2) x x₁ x₂
