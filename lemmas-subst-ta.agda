open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness
open import structural

module lemmas-subst-ta where
  lem-subst-σ : ∀{Δ x Γ τ1 σ Γ' d } →
                  Δ , Γ ,, (x , τ1) ⊢ σ :s: Γ' →
                  Δ , Γ ⊢ d :: τ1 →
                  Δ , Γ ⊢ Subst d x σ :s: Γ'
  lem-subst-σ s wt = STASubst s wt

  exchange-subst-Γ : ∀{Δ Γ x y τ1 τ2 σ Γ'} →
                   Δ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ σ :s: Γ' →
                   Δ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ σ :s: Γ'
  exchange-subst-Γ = {!!}

  data fresh : Nat → dhexp → Set where
    FConst : ∀{x} → fresh x c
    FVar   : ∀{x y} → x ≠ y → fresh x (X y)
    FLam   : ∀{x y τ d} → x ≠ y → fresh x (·λ y [ τ ] d)
    FHole  : ∀{x u σ} → fresh x (⦇⦈⟨ u , σ ⟩)-- todo: should this check into σ, too?
    FNEHole : ∀{x d u σ} → fresh x d → fresh x (⦇ d ⦈⟨ u , σ ⟩)
    FAp     : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x (d1 ∘ d2)
    FCast   : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒ τ2 ⟩)
    FFailedCast : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)

  apart-fresh : ∀{ x Γ Δ d τ} →
                x # Γ →
                Δ , Γ ⊢ d :: τ →
                fresh x d
  apart-fresh aprt TAConst = FConst
  apart-fresh {x = x} aprt (TAVar {x = y} x₂) with natEQ x y
  apart-fresh aprt (TAVar x₃) | Inl refl = abort (somenotnone (! x₃ · aprt))
  apart-fresh aprt (TAVar x₃) | Inr x₂ = FVar x₂
  apart-fresh {x = x} aprt (TALam {x = y} x₂ wt) with natEQ x y
  apart-fresh aprt (TALam x₃ wt) | Inl refl = {!!}
  apart-fresh aprt (TALam x₃ wt) | Inr x₂ = FLam x₂
  apart-fresh aprt (TAAp wt wt₁) = FAp (apart-fresh aprt wt) (apart-fresh aprt wt₁)
  apart-fresh aprt (TAEHole x₁ x₂) = FHole
  apart-fresh aprt (TANEHole x₁ wt x₂) = FNEHole (apart-fresh aprt wt)
  apart-fresh aprt (TACast wt x₁) = FCast (apart-fresh aprt wt)
  apart-fresh aprt (TAFailedCast wt x₁ x₂ x₃) = FFailedCast (apart-fresh aprt wt)


  mutual
    weaken-subst-Γ : ∀{ x Γ Δ σ Γ' τ} →
                     x # Γ →
                     Δ , Γ ⊢ σ :s: Γ' →
                     Δ , (Γ ,, (x , τ)) ⊢ σ :s: Γ'
    weaken-subst-Γ {x = x} {Γ = Γ} {τ = τ1} apt (STAId x₁) = STAId (λ y τ2 x₂ → x∈∪l Γ (■ (x , τ1)) _ _ (x₁ y τ2 x₂))
    weaken-subst-Γ {x = x} {Γ = Γ} {τ = τ1} apt (STASubst {y = y} {τ = τ2} s x₁) with natEQ x y
    weaken-subst-Γ {x = x} {Γ = Γ} {τ = τ1} apt (STASubst {τ = τ2} s x₂) | Inl refl = STASubst {!!} (weaken-ta apt x₂)
    weaken-subst-Γ apt (STASubst s x₂) | Inr x₁ = STASubst {!!} (weaken-ta apt x₂)
    -- = STASubst {!!} (weaken-ta apt x₁)

      -- STASubst (weaken-subst-Γ {x = y} {Γ = Γ ,, (x , τ1)} {τ = τ2} {!!} {!!}) (weaken-ta apt x₁)

    weaken-ta : ∀{x Γ Δ d τ τ'} →
                x # Γ →
                Δ , Γ ⊢ d :: τ →
                Δ , Γ ,, (x , τ') ⊢ d :: τ
    weaken-ta apt TAConst = TAConst
    weaken-ta {x = x} {Γ = Γ} {τ' = τ'} apt (TAVar x₂) = TAVar (x∈∪l Γ  (■ (x , τ')) _ _ x₂)
    weaken-ta apt (TALam x₂ wt) = {!!}
    weaken-ta apt (TAAp wt wt₁) = TAAp (weaken-ta apt wt) (weaken-ta apt wt₁)
    weaken-ta apt (TAEHole x₁ x₂) = TAEHole x₁ (weaken-subst-Γ apt x₂)
    weaken-ta apt (TANEHole x₁ wt x₂) = TANEHole x₁ (weaken-ta apt wt) (weaken-subst-Γ apt x₂)
    weaken-ta apt (TACast wt x₁) = TACast (weaken-ta apt wt) x₁
    weaken-ta apt (TAFailedCast wt x₁ x₂ x₃) = TAFailedCast (weaken-ta apt wt) x₁ x₂ x₃

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
  lem-subst {Γ = Γ} {x = x} apt (TALam  {x = y} x₂ wt1) wt2 = {!(TALam x₂ wt1)!}
  --   with natEQ y x
  -- lem-subst {Γ = Γ} {x = x} apt (TALam x₃ wt1) wt2 | Inl refl = {!!}
  -- lem-subst {Γ = Γ} apt (TALam x₃ wt1) wt2 | Inr x₂
  --   with lem-union-none {Γ = Γ} x₃
  -- ... | _ , r = TALam r (lem-subst {!!} (weaken-ta {!!} {!!}) (weaken-ta r wt2))
  lem-subst apt (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt wt1 wt3) (lem-subst apt wt2 wt3)
  lem-subst apt (TAEHole inΔ sub) wt2 = TAEHole inΔ (lem-subst-σ sub wt2)
  lem-subst apt (TANEHole x₁ wt1 x₂) wt2 = TANEHole x₁ (lem-subst apt wt1 wt2) (lem-subst-σ  x₂ wt2)
  lem-subst apt (TACast wt1 x₁) wt2 = TACast (lem-subst apt wt1 wt2) x₁
  lem-subst apt (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt wt1 wt2) x₁ x₂ x₃


  -- with lem-union-none {Γ = Γ} x₂ | lem-subst apt wt1 {!!}
  -- ... | l , r | ih = TALam r {!ih!}
