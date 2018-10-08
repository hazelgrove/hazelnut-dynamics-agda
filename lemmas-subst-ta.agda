open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

module lemmas-subst-ta where
  --- todo: move this stuff to exchange.agda once it's unholey

  -- note that this is generic in the contents of the context. the proofs
  -- below show the exchange properties that we actually need in the
  -- various other proofs; the remaning exchange properties for both Δ and
  -- Γ positions for all the other hypothetical judgements are exactly in
  -- this pattern.

  -- lem-swap : {A : Set} (Γ : A ctx) (x y : Nat) (t1 t2 : A) {x≠y : x == y → ⊥}  (z : Nat) →
  --        ((Γ ,, (x , t1)) ,, (y , t2)) z == ((Γ ,, (y , t2)) ,, (x , t1)) z
  -- lem-swap Γ x y t1 t2 z with natEQ x z | natEQ y z
  -- lem-swap Γ x y t1 t2 {x≠y} z | Inl p | Inl q = abort (x≠y (p · ! q))
  -- lem-swap Γ x y t1 t2 .x | Inl refl | Inr x₂ with natEQ x x
  -- lem-swap Γ x y t1 t2 .x | Inl refl | Inr x₂ | Inl refl = {!!}
  -- lem-swap Γ x y t1 t2 .x | Inl refl | Inr x₂ | Inr x₁ = abort (x₁ refl)
  -- lem-swap Γ x y t1 t2 .y | Inr x₁ | Inl refl with natEQ y y
  -- lem-swap Γ x₁ y t1 t2 .y | Inr x₂ | Inl refl | Inl refl = {!!}
  -- lem-swap Γ x₁ y t1 t2 .y | Inr x₂ | Inl refl | Inr x = abort (x refl)
  -- lem-swap Γ x y t1 t2 z | Inr x₁ | Inr x₂ with natEQ x z | natEQ y z
  -- lem-swap Γ x .x t1 t2 .x | Inr x₂ | Inr x₃ | Inl refl | Inl refl = abort (x₃ refl)
  -- lem-swap Γ x y t1 t2 .x | Inr x₂ | Inr x₃ | Inl refl | Inr x₁ = abort (x₂ refl)
  -- lem-swap Γ x y t1 t2 z | Inr x₃ | Inr x₄ | Inr x₁ | Inl x₂ = abort (x₄ x₂)
  -- lem-swap Γ x y t1 t2 z | Inr x₃ | Inr x₄ | Inr x₁ | Inr x₂ = {!!}

  swap-little : {A : Set} {x y : Nat} {τ1 τ2 : A} → (x ≠ y) →
    ((■ (x , τ1)) ,, (y , τ2)) == ((■ (y , τ2)) ,, (x , τ1))
  swap-little {A} {x} {y} {τ1} {τ2} neq = ∪comm (■ (x , τ1))
                                                (■ (y , τ2))
                                                (disjoint-singles neq)

  -- toss these if you don't need them
  ctxignore1 : {A : Set} (x : Nat) (C1 C2 : A ctx) → x # C1 → (C1 ∪ C2) x == C2 x
  ctxignore1 x C1 C2 apt with ctxindirect C1 x
  ctxignore1 x C1 C2 apt | Inl x₁ = abort (somenotnone (! (π2 x₁) · apt))
  ctxignore1 x C1 C2 apt | Inr x₁ with C1 x
  ctxignore1 x C1 C2 apt | Inr x₂ | Some x₁ = abort (somenotnone (x₂))
  ctxignore1 x C1 C2 apt | Inr x₁ | None = refl

  -- toss these if you don't need them
  ctxignore2 : {A : Set} (x : Nat) (C1 C2 : A ctx) → x # C2 → (C1 ∪ C2) x == C1 x
  ctxignore2 x C1 C2 apt with ctxindirect C2 x
  ctxignore2 x C1 C2 apt | Inl x₁ = abort (somenotnone (! (π2 x₁) · apt))
  ctxignore2 x C1 C2 apt | Inr x₁ with C1 x
  ctxignore2 x C1 C2 apt | Inr x₂ | Some x₁ = refl
  ctxignore2 x C1 C2 apt | Inr x₁ | None = x₁

  ∪assoc : {A : Set} (C1 C2 C3 : A ctx) → (C2 ## C3) → (C1 ∪ C2) ∪ C3 == C1 ∪ (C2 ∪ C3)
  ∪assoc C1 C2 C3 (d1 , d2) = funext guts
    where
      case2 : (x : Nat) → x # C3 → dom C2 x → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
      case2 x apt dom = (ctxignore2 x (C1 ∪ C2) C3 apt) ·
                        {!!}

-- lem-dom-union1 (d1 , d2) dom

-- tr (λ qq → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ qq) x) {!(ctxignore2 x C2 C3 apt)!} {!!}

      case3 : (x : Nat) → x # C2 → dom C3 x → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
      case3 x apt dom = {!!}

      guts : (x : Nat) → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
      guts x with ctxindirect C2 x | ctxindirect C3 x
      guts x | Inl (π1 , π2) | Inl (π3 , π4) = abort (somenotnone (! π4 · d1 x (π1 , π2)))
      guts x | Inl x₁ | Inr x₂ = case2 x x₂ x₁
      guts x | Inr x₁ | Inl x₂ = case3 x x₁ x₂
      guts x | Inr x₁ | Inr x₂ = {!!}

  swap : {A : Set} (Γ : A ctx) (x y : Nat) (τ1 τ2 : A) (x≠y : x == y → ⊥) →
         ((Γ ,, (x , τ1)) ,, (y , τ2)) == ((Γ ,, (y , τ2)) ,, (x , τ1))
  swap Γ x y τ1 τ2 neq = (∪assoc Γ (■ (x , τ1)) (■ (y , τ2)) (disjoint-singles neq) ) ·
                         (ap1 (λ qq → Γ ∪ qq) (swap-little neq) ·
                          ! (∪assoc Γ (■ (y , τ2)) (■ (x , τ1)) (disjoint-singles (flip neq))))


-- {!tr ? (swap-little {τ1 = τ1} {τ2 = τ2} neq)!}

-- {!ap1 (λ qq → Γ ∪ qq) (swap-little' {τ1 = τ1} {τ2 = τ2} neq)!}

  -- all the proofs of exchange will be almost exactly this one, just with
  -- different judgemental forms in the first argument to transport.
  exchange-subst-Γ : ∀{Δ Γ x y τ1 τ2 σ Γ'} →
                   x ≠ y →
                   Δ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ σ :s: Γ' →
                   Δ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ σ :s: Γ'
  exchange-subst-Γ {Δ} {Γ} {x} {y} {τ1} {τ2} {σ} {Γ'} x≠y xy =
    tr (λ qq → Δ , qq ⊢ σ :s: Γ') (swap Γ x y τ1 τ2 x≠y) xy
     -- tr (λ qq → Δ , qq ⊢ σ :s: Γ') (funext (lem-swap Γ x y τ1 τ2 {x≠y})) xy

  --- todo: move this stuff to weakening.agda once it's unholey
  mutual
    weaken-subst-Γ : ∀{ x Γ Δ σ Γ' τ} →
                     envfresh x σ →
                     Δ , Γ ⊢ σ :s: Γ' →
                     Δ , (Γ ,, (x , τ)) ⊢ σ :s: Γ'
    weaken-subst-Γ {Γ = Γ} (EFId x₁) (STAId x₂) = STAId (λ x τ x₃ → x∈∪l Γ _ x τ (x₂ x τ x₃) )
    weaken-subst-Γ {x = x} {Γ = Γ} (EFSubst x₁ efrsh x₂) (STASubst {y = y} {τ = τ'} subst x₃) =
      STASubst (exchange-subst-Γ {Γ = Γ} (flip x₂) (weaken-subst-Γ {Γ = Γ ,, (y , τ')} efrsh subst))
               (weaken-ta x₁ x₃)

    weaken-ta : ∀{x Γ Δ d τ τ'} →
                fresh x d →
                Δ , Γ ⊢ d :: τ →
                Δ , Γ ,, (x , τ') ⊢ d :: τ
    weaken-ta _ TAConst = TAConst
    weaken-ta {x} {Γ} {_} {_} {τ} {τ'} (FVar x₂) (TAVar x₃) = TAVar (x∈∪l Γ (■ (x , τ')) _ _ x₃)
    weaken-ta {x = x} frsh (TALam {x = y} x₂ wt) with natEQ x y
    weaken-ta (FLam x₁ x₂) (TALam x₃ wt) | Inl refl = abort (x₁ refl)
    weaken-ta {Γ = Γ} {τ' = τ'} (FLam x₁ x₃) (TALam {x = y} x₄ wt) | Inr x₂ = TALam (apart-parts Γ _ _ x₄ (apart-singleton (flip x₁)))
                                                                                    {!weaken-ta {Γ = Γ ,, (y , ?)} x₃ wt!}
    weaken-ta (FAp frsh frsh₁) (TAAp wt wt₁) = TAAp (weaken-ta frsh wt) (weaken-ta frsh₁ wt₁)
    weaken-ta (FHole x₁) (TAEHole x₂ x₃) = TAEHole x₂ (weaken-subst-Γ x₁ x₃)
    weaken-ta (FNEHole x₁ frsh) (TANEHole x₂ wt x₃) = TANEHole x₂ (weaken-ta frsh wt) (weaken-subst-Γ x₁ x₃)
    weaken-ta (FCast frsh) (TACast wt x₁) = TACast (weaken-ta frsh wt) x₁
    weaken-ta (FFailedCast frsh) (TAFailedCast wt x₁ x₂ x₃) = TAFailedCast (weaken-ta frsh wt) x₁ x₂ x₃

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
  lem-subst {Γ = Γ} {x = x} apt (TALam  {x = y} x₂ wt1) wt2 -- = {!weaken-ta ? (TALam x₂ wt1)!}
    with natEQ y x
  lem-subst {Γ = Γ} {x = x} apt (TALam x₃ wt1) wt2 | Inl refl = abort ((π1(lem-union-none {Γ = Γ} x₃)) refl)
  lem-subst {Γ = Γ} apt (TALam x₃ wt1) wt2 | Inr x₂
    with lem-union-none {Γ = Γ} x₃ -- | lem-subst apt wt1  -- probably not the straight IH; need to weaken
  ... | neq , r =  {!!}             --  TALam r (lem-subst {!!} (weaken-ta {!!} {!!}) (weaken-ta r wt2))
  lem-subst apt (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt wt1 wt3) (lem-subst apt wt2 wt3)
  lem-subst apt (TAEHole inΔ sub) wt2 = TAEHole inΔ (STASubst sub wt2)
  lem-subst apt (TANEHole x₁ wt1 x₂) wt2 = TANEHole x₁ (lem-subst apt wt1 wt2) (STASubst x₂ wt2)
  lem-subst apt (TACast wt1 x₁) wt2 = TACast (lem-subst apt wt1 wt2) x₁
  lem-subst apt (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt wt1 wt2) x₁ x₂ x₃
