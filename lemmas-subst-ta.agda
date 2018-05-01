open import Prelude
open import Nat
open import core
open import contexts

open import structural
module lemmas-subst-ta where
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } →
                  x # Γ →
                  Δ , Γ ,, (x , τ1) ⊢ d1 :: τ →
                  Δ , Γ ⊢ d2 :: τ1 →
                  Δ , Γ ⊢ [ d2 / x ] d1 :: τ
  lem-subst apt TAConst wt2 = TAConst
  lem-subst {x = x} apt (TAVar {x = x'} x₂) wt2 with natEQ x' x
  lem-subst {Γ = Γ} apt (TAVar x₃) wt2 | Inl refl with lem-apart-union-eq {Γ = Γ} apt x₃
  lem-subst apt (TAVar x₃) wt2 | Inl refl | refl = wt2
  lem-subst {Γ = Γ} apt (TAVar x₃) wt2 | Inr x₂ = TAVar (lem-neq-union-eq {Γ = Γ} x₂ x₃)
  lem-subst {Γ = Γ} apt (TALam x₂ wt1) wt2 with lem-union-none {Γ = Γ} x₂
  ... | l , r = TALam r {!lem-subst {Γ = } ? wt1 ? !}
  lem-subst apt (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt wt1 wt3) (lem-subst apt wt2 wt3)
  lem-subst apt (TAEHole x₁ x₂) wt2 with x₂ {!!} {!!} {!!} -- definitely going to need to call x₂ on something; no idea whay
  lem-subst apt (TAEHole x₁ x₂) wt2 | π1 , π2 , π3 = TAEHole x₁ (λ x d xd∈σ → {!!}) -- this is the shape we'll get back
  lem-subst apt (TANEHole x₁ wt1 x₂) wt2 = TANEHole x₁ (lem-subst apt wt1 wt2) {!!} -- this will go mostly like the above hole
  lem-subst apt (TACast wt1 x₁) wt2 = TACast (lem-subst apt wt1 wt2) x₁
  lem-subst apt (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt wt1 wt2) x₁ x₂ x₃

      -- (λ x →
      --    (Γ ∪ ■ (.x , .τ1)) ∪ ■  (.x₁ , .τ2)

      --    (λ y →  y | natEQ .x₁ y) x
      --    | (Γ ∪ (λ y → ■_ (.x , .τ1) y | natEQ .x y) x
      --       | Γ x))
