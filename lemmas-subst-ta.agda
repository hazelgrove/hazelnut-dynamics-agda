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
  data var-name-new : (x : Nat) (d : dhexp) → Set where
    VNNConst : ∀{x} → var-name-new x c
    VNNVar : ∀{x y} → x ≠ y → var-name-new x (X y)
    VNNLam2 : ∀{x d y τ} → x ≠ y
                         → var-name-new x d
                         → var-name-new x (·λ_[_]_ y τ d)
    VNNHole : ∀{x u σ} → var-name-new x (⦇⦈⟨ u , σ ⟩) -- todo something about σ?
    VNNNEHole : ∀{x u σ d } →
                var-name-new x d →
                var-name-new x (⦇ d ⦈⟨ u , σ ⟩) -- todo something about σ?
    VNNAp : ∀{ x d1 d2 } →
           var-name-new x d1 →
           var-name-new x d2 →
           var-name-new x (d1 ∘ d2)
    VNNCast : ∀{x d τ1 τ2} → var-name-new x d → var-name-new x (d ⟨ τ1 ⇒ τ2 ⟩)
    VNNFailedCast : ∀{x d τ1 τ2} → var-name-new x d → var-name-new x (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)

  -- two terms that do not share any hole names
  data var-names-disjoint : (d1 : dhexp) → (d2 : dhexp) → Set where
    VNDConst : ∀{d} → var-names-disjoint c d
    VNDVar : ∀{x d} → var-names-disjoint (X x) d
    VNDLam : ∀{x τ d1 d2} → var-names-disjoint d1 d2
                          → var-names-disjoint (·λ_[_]_ x τ d1) d2
    VNDHole : ∀{u σ d2} → var-name-new u d2
                        → var-names-disjoint (⦇⦈⟨ u , σ ⟩) d2 -- todo something about σ?
    VNDNEHole : ∀{u σ d1 d2} → var-name-new u d2
                             → var-names-disjoint d1 d2
                             → var-names-disjoint (⦇ d1 ⦈⟨ u , σ ⟩) d2 -- todo something about σ?
    VNDAp :  ∀{d1 d2 d3} → var-names-disjoint d1 d3
                         → var-names-disjoint d2 d3
                         → var-names-disjoint (d1 ∘ d2) d3

  -- all the variable names in the term are unique
  data var-names-unique : dhexp → Set where
    VNUHole : var-names-unique c
    VNUVar : ∀{x} → var-names-unique (X x)
    VNULam : {x : Nat} {τ : htyp} {d : dhexp} → var-names-unique d
                                              → var-name-new x d
                                              → var-names-unique (·λ_[_]_ x τ d)
    VNUEHole : ∀{u σ} → var-names-unique (⦇⦈⟨ u , σ ⟩) -- todo something about σ?
    VNUNEHole : ∀{u σ d} → var-names-unique d
                         → var-names-unique (⦇ d ⦈⟨ u , σ ⟩) -- todo something about σ?
    VNUAp : ∀{d1 d2} → var-names-unique d1
                     → var-names-unique d2
                     → var-names-disjoint d1 d2
                     → var-names-unique (d1 ∘ d2)
    VNUCast : ∀{d τ1 τ2} → var-names-unique d
                         → var-names-unique (d ⟨ τ1 ⇒ τ2 ⟩)
    VNUFailedCast : ∀{d τ1 τ2} → var-names-unique d
                               → var-names-unique (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)

  unique-fresh : ∀{Δ Γ d τ y} → Δ , Γ ⊢ d :: τ → y # Γ → var-names-unique d → fresh y d
  unique-fresh TAConst apt VNUHole = FConst
  unique-fresh (TAVar x₁) apt VNUVar = {!!}
  unique-fresh (TALam x₁ wt) apt (VNULam unq x₂) = {!!}
  unique-fresh (TAAp wt wt₁) apt (VNUAp unq unq₁ x) = {!!}
  unique-fresh (TAEHole x x₁) apt VNUEHole = {!!}
  unique-fresh (TANEHole x wt x₁) apt (VNUNEHole unq) = {!!}
  unique-fresh (TACast wt x) apt (VNUCast unq) = {!!}
  unique-fresh (TAFailedCast wt x x₁ x₂) apt (VNUFailedCast unq) = {!!}

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
