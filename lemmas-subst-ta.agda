open import Prelude
open import Nat
open import List
open import core
open import contexts
open import weakening
open import exchange
open import lemmas-disjointness

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
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d2 = d2} x#Γ (TALam {x = y} {τ1 = τ1} {d = d} {τ2 = τ2} x₂ wt1) wt2
    with lem-union-none {Γ = Γ} x₂
  ... |  x≠y , y#Γ with natEQ y x
  ... | Inl eq = abort (x≠y (! eq))
  ... | Inr _ with exists-fresh d2
  ... | z , neq = TALam y#Γ (lem-subst {Δ = Δ} {Γ = Γ ,, (y , τ1)} {x = x} {d1 = d} (apart-extend1 Γ x≠y x#Γ) (exchange-ta-Γ {Γ = Γ} x≠y wt1) (weaken-ta {!!} wt2))
  lem-subst apt (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt wt1 wt3) (lem-subst apt wt2 wt3)
  lem-subst apt (TAEHole inΔ sub) wt2 = TAEHole inΔ (STASubst sub wt2)
  lem-subst apt (TANEHole x₁ wt1 x₂) wt2 = TANEHole x₁ (lem-subst apt wt1 wt2) (STASubst x₂ wt2)
  lem-subst apt (TACast wt1 x₁) wt2 = TACast (lem-subst apt wt1 wt2) x₁
  lem-subst apt (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt wt1 wt2) x₁ x₂ x₃

  -- possible fix: add a premise from a new judgement like holes disjoint
  -- that classifies pairs of dhexps that share no variable names
  -- whatsoever. that should imply freshness here. then propagate that
  -- change to preservation. this is morally what α-equiv lets us do in a
  -- real setting.


  -- lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d2 = d2} x#Γ (TALam {x = y} {τ1 = τ1} {d = d} {τ2 = τ2} x₂ wt1) wt2
  --   with lem-union-none {Γ = Γ} x₂
  -- ... |  x≠y , y#Γ with natEQ y x
  -- ... | Inl eq = abort (x≠y (! eq))
  -- ... | Inr _ with exists-fresh d2 None
  -- ... | z , neq = TALam y#Γ (lem-subst {Δ = Δ} {Γ = Γ ,, (y , τ1)} {x = x} {d1 = d} (apart-extend1 Γ x≠y x#Γ) (exchange-ta-Γ {Γ = Γ} x≠y wt1) (weaken-ta {!!} wt2))
