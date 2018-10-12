open import Prelude
open import Nat
open import List
open import core
open import contexts
open import weakening
open import exchange
open import lemmas-disjointness

module lemmas-subst-ta where
  -- todo: add a premise from a new judgement like holes disjoint that
  -- classifies pairs of dhexps that share no variable names
  -- whatsoever. that should imply freshness here. then propagate that
  -- change to preservation. this is morally what α-equiv lets us do in a
  -- real setting.

  -- the variable name x does not appear in the term d
  data var-name-new : (d : dhexp) (x : Nat) → Set where
    VNConst : ∀{x} → var-name-new c x
    VNVar : ∀{x y} → x ≠ y → var-name-new (X y) x
    VNLam2 : ∀{x e y τ} →
             x ≠ y →
             var-name-new e x →
             var-name-new (·λ_[_]_ y τ e) x
    -- VNHole : ∀{x u σ} →
    --           -- →
    --          var-name-new (⦇⦈[ u , σ ]) x
    -- VNNEHole : ∀{u u' e} →
    --            u' ≠ u →
    --            var-name-new e u →
    --            var-name-new (⦇ e ⦈[ u' ]) u
    -- VNAp : ∀{ u e1 e2 } →
    --        var-name-new e1 u →
    --        var-name-new e2 u →
    --        var-name-new (e1 ∘ e2) u

  -- two terms that do not share any hole names
  data vars-disjoint : (e1 : hexp) → (e2 : hexp) → Set where
    -- HDConst : ∀{e} → holes-disjoint c e
    -- HDAsc : ∀{e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (e1 ·: τ) e2
    -- HDVar : ∀{x e} → holes-disjoint (X x) e
    -- HDLam1 : ∀{x e1 e2} → holes-disjoint e1 e2 → holes-disjoint (·λ x e1) e2
    -- HDLam2 : ∀{x e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (·λ x [ τ ] e1) e2
    -- HDHole : ∀{u e2} → hole-name-new e2 u → holes-disjoint (⦇⦈[ u ]) e2
    -- HDNEHole : ∀{u e1 e2} → hole-name-new e2 u → holes-disjoint e1 e2 → holes-disjoint (⦇ e1 ⦈[ u ]) e2
    -- HDAp :  ∀{e1 e2 e3} → holes-disjoint e1 e3 → holes-disjoint e2 e3 → holes-disjoint (e1 ∘ e2) e3


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
  ... | Inr _  = TALam y#Γ (lem-subst {Δ = Δ} {Γ = Γ ,, (y , τ1)} {x = x} {d1 = d} (apart-extend1 Γ x≠y x#Γ) (exchange-ta-Γ {Γ = Γ} x≠y wt1) (weaken-ta {!!} wt2))
  lem-subst apt (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt wt1 wt3) (lem-subst apt wt2 wt3)
  lem-subst apt (TAEHole inΔ sub) wt2 = TAEHole inΔ (STASubst sub wt2)
  lem-subst apt (TANEHole x₁ wt1 x₂) wt2 = TANEHole x₁ (lem-subst apt wt1 wt2) (STASubst x₂ wt2)
  lem-subst apt (TACast wt1 x₁) wt2 = TACast (lem-subst apt wt1 wt2) x₁
  lem-subst apt (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt wt1 wt2) x₁ x₂ x₃
