open import Prelude
open import Nat
open import core
open import contexts

open import structural
module lemmas-subst-ta where
  lem-subst-σ : ∀{Δ x Γ τ1 σ Γ' d } →
                  x # Γ →
                  Δ , Γ ,, (x , τ1) ⊢ σ :s: Γ' →
                  Δ , Γ ⊢ d :: τ1 →
                  Δ , Γ ⊢ Subst d x σ :s: Γ'
  lem-subst-σ {Γ' = Γ'} apt (STAId subset) wt = STASubst (STAId {!!}) wt
  lem-subst-σ apt (STASubst s x₁) wt = STASubst (lem-subst-σ {!!} {!!} {!!}) wt

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
  lem-subst {Γ = Γ} apt (TALam x₂ wt1) wt2 with lem-union-none {Γ = Γ} x₂ | lem-subst apt wt1 {!!}
  ... | l , r | ih = TALam r {!ih!}
  lem-subst apt (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt wt1 wt3) (lem-subst apt wt2 wt3)
  lem-subst apt (TAEHole inΔ sub) wt2 = TAEHole inΔ (lem-subst-σ apt sub wt2)
  lem-subst apt (TANEHole x₁ wt1 x₂) wt2 = TANEHole x₁ (lem-subst apt wt1 wt2) (lem-subst-σ apt x₂ wt2)
  lem-subst apt (TACast wt1 x₁) wt2 = TACast (lem-subst apt wt1 wt2) x₁
  lem-subst apt (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt wt1 wt2) x₁ x₂ x₃
