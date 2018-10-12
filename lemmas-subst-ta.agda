open import Prelude
open import Nat
open import core
open import contexts
open import weakening
open import exchange
open import lemmas-disjointness

module lemmas-subst-ta where
  -- there is always a natural number that's fresh for any expression,
  -- possibly avoiding one in particular
  exists-fresh : (d : dhexp) → Σ[ y ∈ Nat ] (fresh y d)
  exists-fresh = {!!}

  -- rename all x's into y's in d to produce d'
  data rename : (x : Nat) → (y : Nat) → (d : dhexp) (d' : dhexp) → Set where
    RConst       : ∀{x y} → rename x y c c
    RVar1        : ∀{x y z} → x ≠ z → rename x y (X z) (X z)
    RVar2        : ∀{x y} → rename x y (X x) (X y)
  --  RLam         : ∀{x y τ e} → rename x y ? ?
    -- REHole
    -- RNEHole
    -- RAp
    -- RCast
    -- RFailedCast

  -- have to do something about the context in the typing judgement as well
  -- and probably in the σs. bleh.

  exists-rename : (x y : Nat) (d : dhexp) → Σ[ d' ∈ dhexp ](rename x y d d')
  exists-rename z y c = c , RConst
  exists-rename z y (X x) with natEQ z x
  exists-rename z y (X .z) | Inl refl = X y , RVar2
  exists-rename z y (X x) | Inr x₁ = X x , RVar1 x₁
  exists-rename z y (·λ x [ x₁ ] d) = {!!}
  exists-rename z y ⦇⦈⟨ x ⟩ = {!!}
  exists-rename z y ⦇ d ⦈⟨ x ⟩ = {!!}
  exists-rename z y (d ∘ d₁) = {!!}
  exists-rename z y (d ⟨ x ⇒ x₁ ⟩) = {!!}
  exists-rename z y (d ⟨ x ⇒⦇⦈⇏ x₁ ⟩) = {!!}

  rename-ctx : {A : Set} → (x y : Nat) → (Γ : A ctx) → A ctx
  rename-ctx x y Γ q with natEQ y q -- if you're asking about the new variable y,  it's now gonna be  whatever x was
  rename-ctx x y Γ q | Inl x₁ = Γ x
  rename-ctx x y Γ q | Inr x₁ = Γ q

  -- is this the right direction? try to use it below; need that y # Γ, likely
  rename-preserve : ∀{x y d d' Δ Γ τ} → (f : fresh y d) → rename x y d d' → Δ , Γ ⊢ d :: τ → Δ , (rename-ctx x y Γ) ⊢ d' :: τ
  rename-preserve FConst RConst TAConst = TAConst
  rename-preserve (FVar x₂) (RVar1 x₁) (TAVar x₃) = TAVar {!!}
  rename-preserve (FVar x₂) RVar2 (TAVar x₃) = TAVar {!!}
  rename-preserve (FLam x₂ f) re (TALam x₃ wt) = {!!}
  rename-preserve (FHole x₂) re (TAEHole x₃ x₄) = {!!}
  rename-preserve (FNEHole x₂ f) re (TANEHole x₃ wt x₄) = {!!}
  rename-preserve (FAp f f₁) re (TAAp wt wt₁) = {!!}
  rename-preserve (FCast f) re (TACast wt x₂) = {!!}
  rename-preserve (FFailedCast f) re (TAFailedCast wt x₂ x₃ x₄) = {!!}

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
