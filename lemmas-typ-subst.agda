open import Nat
open import Prelude
open import core
open import contexts

open import rewrite-util

module lemmas-typ-subst where

  t-sub-id : ∀{τ τ' t} →
    tfresht t τ →
    Typ[ τ' / t ] τ == τ
  t-sub-id TFBase = refl
  t-sub-id (TFTVar x) rewrite natEQneq x = refl
  t-sub-id TFHole = refl
  t-sub-id (TFArr tft1 tft2) = arr-eq (t-sub-id tft1) (t-sub-id tft2)
  t-sub-id (TFForall x tft) rewrite natEQneq x = forall-eq refl (t-sub-id tft)

  tctx-sub-id : ∀{Γ t τ} →
    tfresh-in-Γ t Γ →
    Tctx[ τ / t ] Γ == Γ
  tctx-sub-id {Γ} {t} {τ} (TFΓ ubig) = funext (λ x → foo x)
    where
      foo : (x : Nat) -> (Tctx[ τ / t ] Γ) x == Γ x
      foo x with ctxindirect (Tctx[ τ / t ] Γ) x | ctxindirect Γ x
      ... | Inl (y1 , ing1) | Inl (y2 , ing2) rewrite ing2 = some-epi (t-sub-id (ubig x y2 ing2))
      ... | Inr nig1 | Inr nig2 rewrite nig1 rewrite nig2 = refl
      ... | Inl (y1 , ing1) | Inr nig2 rewrite ing1 rewrite nig2 = abort (somenotnone (! ing1))
      ... | Inr nig1 | Inl (y2 , ing2) rewrite nig1 rewrite ing2 = abort (somenotnone nig1)

  t-sub-idem : ∀{τ t} → (τ0 : htyp) → ∅ ⊢ τ wf → Typ[ τ / t ] (Typ[ τ / t ] τ0) == Typ[ τ / t ] τ0
  t-sub-idem t0 wf = {!   !}

  tctx-sub-idem : ∀{τ t} → (Γ : tctx) → ∅ ⊢ τ wf → Tctx[ τ / t ] (Tctx[ τ / t ] Γ) == Tctx[ τ / t ] Γ
  tctx-sub-idem Γ wf = funext (λ x → foo x Γ wf)
    where
      foo : ∀{τ t} → (x : Nat) → (Γ : tctx) → ∅ ⊢ τ wf → (Tctx[ τ / t ] (Tctx[ τ / t ] Γ)) x == (Tctx[ τ / t ] Γ) x
      foo {τ} {t} x Γ wf with ctxindirect Γ x
      ... | Inl (y , ing) rewrite ing rewrite t-sub-idem {τ} {t} y wf = refl
      ... | Inr nig rewrite nig = refl

  t-sub-unit : ∀{τ τ' t Θ} →
    t # Θ -> Θ ⊢ τ wf → Typ[ τ' / t ] τ == τ
  t-sub-unit apt WFBase = refl
  t-sub-unit apt WFHole = refl
  t-sub-unit {t = t} apt (WFVar {a = t'} mem) with natEQ t t'
  ... | Inl refl = abort (somenotnone ((! mem) · apt))
  ... | Inr neq = refl
  t-sub-unit apt (WFArr wf1 wf2) = arr-eq (t-sub-unit apt wf1) (t-sub-unit apt wf2)
  t-sub-unit {t = t} {Θ = Θ} apt (WFForall {n = t'} wf) with natEQ t t'
  ... | Inl refl = refl
  ... | Inr neq = forall-eq refl (t-sub-unit (lem-apart-extend {Γ = Θ} apt neq) wf)

  t-sub-closed : ∀{τ τ' t} →
    ∅ ⊢ τ wf → Typ[ τ' / t ] τ == τ
  t-sub-closed wf = t-sub-unit refl wf

  tctx-sub-closed : ∀{Γ t τ} → ∅ ⊢ Γ tctxwf → Tctx[ τ / t ] Γ == Γ
  tctx-sub-closed {Γ} {t} {τ} (CCtx tcwf) = funext (λ x → foo x)
    where
      foo : (x : Nat) -> (Tctx[ τ / t ] Γ) x == Γ x
      foo x with ctxindirect (Tctx[ τ / t ] Γ) x | ctxindirect Γ x
      ... | Inl (y1 , ing1) | Inl (y2 , ing2) rewrite ing2 = some-epi (t-sub-closed (tcwf ing2))
      ... | Inr nig1 | Inr nig2 rewrite nig1 rewrite nig2 = refl
      ... | Inl (y1 , ing1) | Inr nig2 rewrite ing1 rewrite nig2 = abort (somenotnone (! ing1))
      ... | Inr nig1 | Inl (y2 , ing2) rewrite nig1 rewrite ing2 = abort (somenotnone nig1)

  t-sub-comm :  ∀{τ' τ'' t' t''} → (τ : htyp) →
    ∅ ⊢ τ' wf → ∅ ⊢ τ'' wf → t' ≠ t'' → Typ[ τ'' / t'' ] (Typ[ τ' / t' ] τ) == Typ[ τ' / t' ] (Typ[ τ'' / t'' ] τ)
  t-sub-comm b wf1 wf2 ne = refl
  t-sub-comm {t' = t'} {t'' = t''} (T x) wf1 wf2 ne with natEQ t' x | natEQ t'' x
  ... | Inl refl | Inl refl = abort (ne refl)
  ... | Inl refl | Inr neq'' rewrite natEQrefl {x = t'} = t-sub-closed wf1
  ... | Inr neq' | Inl refl rewrite natEQrefl {x = t''} = ! (t-sub-closed wf2)
  ... | Inr neq' | Inr neq'' rewrite natEQneq neq' rewrite natEQneq neq'' = refl
  t-sub-comm ⦇-⦈ wf1 wf2 ne = refl
  t-sub-comm (τ1 ==> τ2) wf1 wf2 ne = arr-eq (t-sub-comm τ1 wf1 wf2 ne) (t-sub-comm τ2 wf1 wf2 ne)
  t-sub-comm {t' = t'} {t'' = t''} (·∀ t τ) wf1 wf2 ne with natEQ t' t | natEQ t'' t
  ... | Inl refl | Inl refl = abort (ne refl)
  ... | Inl refl | Inr neq'' rewrite natEQrefl {x = t'} rewrite natEQneq neq'' = refl
  ... | Inr neq' | Inl refl rewrite natEQrefl {x = t''} rewrite natEQneq neq' = refl
  ... | Inr neq' | Inr neq'' rewrite natEQneq neq' rewrite natEQneq neq'' = forall-eq refl (t-sub-comm τ wf1 wf2 ne)
  
  tctx-sub-comm : ∀{τ' τ'' t' t''} → (Γ : tctx) →
    ∅ ⊢ τ' wf → ∅ ⊢ τ'' wf → t' ≠ t'' → Tctx[ τ'' / t'' ] (Tctx[ τ' / t' ] Γ) == Tctx[ τ' / t' ] (Tctx[ τ'' / t'' ] Γ)
  tctx-sub-comm Γ wf1 wf2 ne = {!   !}

  ihexp-sub-comm : ∀{τ' τ'' t' t''} → (d : ihexp) →
    ∅ ⊢ τ' wf → ∅ ⊢ τ'' wf → t' ≠ t'' → Ihexp[ τ'' / t'' ] (Ihexp[ τ' / t' ] d) == Ihexp[ τ' / t' ] (Ihexp[ τ'' / t'' ] d)
  ihexp-sub-comm d wf1 wf2 ne = {!   !}

  sub-sub-comm : ∀{τ' τ'' t' t''} → (σ : env) →
    ∅ ⊢ τ' wf → ∅ ⊢ τ'' wf → t' ≠ t'' → Sub[ τ'' / t'' ] (Sub[ τ' / t' ] σ) == Sub[ τ' / t' ] (Sub[ τ'' / t'' ] σ)
  sub-sub-comm (Id Γ) wf1 wf2 ne rewrite tctx-sub-comm Γ wf1 wf2 ne = refl
  sub-sub-comm (Subst d y ts) wf1 wf2 ne = subst-eq (ihexp-sub-comm d wf1 wf2 ne) refl (sub-sub-comm ts wf1 wf2 ne)

  alpha-sub : ∀{τ t1 τ1 t2 τ2} → ·∀ t1 τ1 =α ·∀ t2 τ2 → (Typ[ τ / t1 ] τ1) =α (Typ[ τ / t2 ] τ2)
  alpha-sub alpha = {!   !}

  consist-sub : ∀{τ t1 τ1 t2 τ2} → ·∀ t1 τ1 ~ ·∀ t2 τ2 → (Typ[ τ / t1 ] τ1) ~ (Typ[ τ / t2 ] τ2)
  consist-sub consis = {!   !}