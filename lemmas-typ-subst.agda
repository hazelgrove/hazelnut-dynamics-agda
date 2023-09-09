{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open import contexts

open import weakening
open import lemmas-alpha

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

  t-sub-wf : ∀{Θ τ τ' t} →
    Θ ⊢ τ wf → Θ ⊢ τ' wf → Θ ⊢ (Typ[ τ' / t ] τ) wf
  t-sub-wf {t = t} (WFVar {a = a} x) wf' with natEQ t a
  ... | Inl refl = wf'
  ... | Inr neq = WFVar x
  t-sub-wf WFBase wf' = WFBase
  t-sub-wf WFHole wf' = WFHole
  t-sub-wf (WFArr wf wf₁) wf' = WFArr (t-sub-wf wf wf') (t-sub-wf wf₁ wf')
  t-sub-wf {t = t} (WFForall {n = n} wf) wf' with natEQ t n
  ... | Inl refl = WFForall wf
  ... | Inr neq = WFForall (t-sub-wf wf (weaken-t-wf wf'))

  tctx-sub-wf : ∀{Θ Γ τ t} →
    Θ ⊢ Γ tctxwf → Θ ⊢ τ wf → Θ ⊢ (Tctx[ τ / t ] Γ) tctxwf
  tctx-sub-wf {Θ} {Γ} {τ} {t} (CCtx tcwf) wf = CCtx (λ {x} {y} mem → foo x y mem)
    where
      foo : (x : Nat) → (y : htyp) → (x , y) ∈ (Tctx[ τ / t ] Γ) → Θ ⊢ y wf
      foo x y mem with ctxindirect Γ x
      ... | Inr nil rewrite nil = abort (somenotnone (! mem))
      ... | Inl (y' , inl) rewrite inl rewrite ! (someinj mem) = t-sub-wf (tcwf inl) wf

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

  open alpha
  
  ctx-lextend-exchange : ∀{A x x' y y'} → (Γ : A ctx) → x ≠ y → (■ (y , y')) ∪ ((■ (x , x')) ∪ Γ) == (■ (x , x')) ∪ ((■ (y , y')) ∪ Γ)
  ctx-lextend-exchange {x = x} {x'} {y} {y'} Γ ne = funext foo
    where
      foo : (w : Nat) → ((■ (y , y')) ∪ ((■ (x , x')) ∪ Γ)) w == ((■ (x , x')) ∪ ((■ (y , y')) ∪ Γ)) w
      foo w with natEQ y w | natEQ x w
      ... | Inl refl | Inl refl rewrite natEQrefl {w} = abort (ne refl)
      ... | Inr neq | Inl refl rewrite natEQrefl {w} = refl
      ... | Inl refl | Inr neq rewrite natEQrefl {w} = refl
      ... | Inr neq | Inr neq' rewrite natEQneq neq rewrite natEQneq neq' = refl

  lem-extend-refl : ∀{Θ n} → (n' : Nat) → (Γ : Nat ctx) → ((t : Nat) → (t , <>) ∈ Θ → ((t , t) ∈ Γ)) → (n' , <>) ∈ (Θ ,, (n , <>)) → (n' , n') ∈ ((■ (n , n)) ∪ Γ)
  lem-extend-refl {Θ} {n} n' Γ cond mem with natEQ n n'
  ... | Inl refl rewrite natEQrefl {n'} = refl
  ... | Inr neq with ctxindirect Θ n'
  ...   | Inl (<> , int) rewrite natEQneq neq rewrite cond n' int = refl
  ...   | Inr nit rewrite nit rewrite natEQneq neq = abort (somenotnone (! mem))

  wf-alpha-refl : ∀{ΓL ΓR Θ τ} → Θ ⊢ τ wf → ((t : Nat) → (t , <>) ∈ Θ → (t , t) ∈ ΓL × (t , t) ∈ ΓR) → ΓL , ΓR ⊢ τ =α τ
  wf-alpha-refl (WFVar {a = a} x) cond = AlphaVarBound (π1 (cond a x)) (π2 (cond a x))
  wf-alpha-refl WFBase cond = AlphaBase
  wf-alpha-refl WFHole cond = AlphaHole
  wf-alpha-refl (WFArr wf wf₁) cond = AlphaArr (wf-alpha-refl wf cond) (wf-alpha-refl wf₁ cond)
  wf-alpha-refl {ΓL} {ΓR} {Θ = Θ} (WFForall {n = n} wf) cond = AlphaForall (wf-alpha-refl wf (λ t₁ x → lem-extend-refl t₁ ΓL (λ t z → π1 (cond t z)) x , lem-extend-refl t₁ ΓR (λ t z → π2 (cond t z)) x))

  closed-alpha-refl : ∀{ΓL ΓR τ} → ∅ ⊢ τ wf → ΓL , ΓR ⊢ τ =α τ
  closed-alpha-refl wf = wf-alpha-refl wf λ t x → abort (somenotnone (! x))

  ctx-lshadow : ∀{A x y z} → (Γ : A ctx) → (■ (x , y)) ∪ ((■ (x , z)) ∪ Γ) == ((■ (x , y)) ∪ Γ)
  ctx-lshadow {x = x} {y} {z} Γ = funext foo
    where
      foo : (x' : Nat) → ((■ (x , y)) ∪ ((■ (x , z)) ∪ Γ)) x' == ((■ (x , y)) ∪ Γ) x'
      foo x' with natEQ x x'
      ... | Inl refl rewrite natEQrefl {x} = refl
      ... | Inr neq rewrite natEQneq neq = refl

  lem-alpha-sub-forall-asym : ∀{x t1 t2 τ1 τ2 τ ΓL ΓR} → x ≠ t1 → ((■ (x , t2)) ∪ ((■ (t1 , t2)) ∪ ΓL)) , (■ (t2 , x)) ∪ ΓR ⊢ τ1 =α τ2 → (Typ[ τ / t1 ] τ1) == τ1
  lem-alpha-sub-forall-asym ne AlphaBase = refl
  lem-alpha-sub-forall-asym {x} {t1 = t1} {t2} ne (AlphaVarBound {x = x'} {y = y} meml memr) with natEQ t1 x'
  ... | Inr neq = refl
  ... | Inl refl with natEQ t2 y
  ...   | Inl refl = abort (ne (someinj memr))
  ...   | Inr neq with natEQ x t1
  ...     | Inl refl = abort (ne refl)
  ...     | Inr neq' rewrite natEQrefl {t1} = abort (neq (someinj meml))
  lem-alpha-sub-forall-asym ne (AlphaVarFree x x₁) = {!   !}
  lem-alpha-sub-forall-asym ne AlphaHole = refl
  lem-alpha-sub-forall-asym ne (AlphaArr alpha alpha₁) = arr-eq (lem-alpha-sub-forall-asym ne alpha) (lem-alpha-sub-forall-asym ne alpha₁)
  lem-alpha-sub-forall-asym ne (AlphaForall alpha) = {!   !}

  lem-apt-extendl2 : ∀{z x' y'} → (x y : Nat) → (Γ : Nat ctx) → z # ((■ (x , y)) ∪ ((■ (x' , y')) ∪ Γ)) → z # ((■ (x , y)) ∪ Γ)
  lem-apt-extendl2 {z} {x'} x y Γ apt with natEQ x z
  ... | Inl refl rewrite natEQrefl {z} = apt
  ... | Inr neq rewrite natEQneq neq with natEQ x' z 
  ...   | Inl refl = abort (somenotnone apt)
  ...   | Inr neq' = apt

  lem-alpha-prunel1 : ∀{τ1 τ2} → (ΓL ΓR : Nat ctx) → (x y x' : Nat) → ((■ (x , y)) ∪ ((■ (x' , y)) ∪ ΓL)) , (■ (y , x)) ∪ ΓR ⊢ τ1 =α τ2 → ((■ (x , y)) ∪ ΓL) , (■ (y , x)) ∪ ΓR ⊢ τ1 =α τ2
  lem-alpha-prunel1 ΓL ΓR x y x' AlphaBase = AlphaBase
  lem-alpha-prunel1 ΓL ΓR x y x' (AlphaVarBound {x = z} x₁ x₂) = AlphaVarBound {!   !} {!   !}
  lem-alpha-prunel1 ΓL ΓR x y x' (AlphaVarFree {x = z} x₁ x₂) = AlphaVarFree (lem-apt-extendl2 {z = z} {x' = x'} {y' = y} x y ΓL x₁) x₂
  lem-alpha-prunel1 ΓL ΓR x y x' AlphaHole = {!   !}
  lem-alpha-prunel1 ΓL ΓR x y x' (AlphaArr alpha alpha₁) = {!   !}
  lem-alpha-prunel1 ΓL ΓR x y x' (AlphaForall alpha) = {!   !}

  lem-alpha-pruner1 : ∀{τ1 τ2} → (ΓL ΓR : Nat ctx) → (x y y' : Nat) → ((■ (x , y)) ∪ ΓL) , ((■ (y , x)) ∪ ((■ (y' , x)) ∪ ΓR)) ⊢ τ1 =α τ2 → ((■ (x , y)) ∪ ΓL) , (■ (y , x)) ∪ ΓR ⊢ τ1 =α τ2
  lem-alpha-pruner1 ΓL ΓR x y y' alpha = {!   !}

  ⊢alpha-sub : ∀{τ t1 τ1 t2 τ2 ΓL ΓR} → ∅ ⊢ τ wf → ((■ (t1 , t2)) ∪ ΓL) , (■ (t2 , t1)) ∪ ΓR ⊢ τ1 =α τ2 → ΓL , ΓR ⊢ (Typ[ τ / t1 ] τ1) =α (Typ[ τ / t2 ] τ2)
  ⊢alpha-sub {τ1 = b} {τ2 = b} _ alpha = AlphaBase
  ⊢alpha-sub {t1 = t1} {τ1 = T x} {t2 = t2} {τ2 = T x'} wf (AlphaVarBound x₂ x₃) with natEQ t1 x | natEQ t2 x' 
  ... | Inr neq | Inr neq' = AlphaVarBound x₂ x₃
  ... | Inl refl | Inr neq = abort (neq (someinj x₂))
  ... | Inr neq | Inl refl = abort (neq (someinj x₃))
  ... | Inl refl | Inl refl = closed-alpha-refl wf
  ⊢alpha-sub {t1 = t1} {τ1 = T x} {t2 = t2} {τ2 = T .x} wf (AlphaVarFree x₁ x₂) with natEQ t1 x | natEQ t2 x
  ... | Inr neq | Inr neq' = AlphaVarFree x₁ x₂
  ... | _ | Inl refl = abort (somenotnone x₂)
  ... | Inl refl | _ = abort (somenotnone x₁)
  ⊢alpha-sub {τ1 = ⦇-⦈} {τ2 = ⦇-⦈} _ alpha = AlphaHole
  ⊢alpha-sub {τ1 = τ1 ==> τ3} {τ2 = τ2 ==> τ4} wf (AlphaArr alpha alpha₁) = AlphaArr (⊢alpha-sub wf alpha) (⊢alpha-sub wf alpha₁)
  ⊢alpha-sub {τ} {t1 = t1} {τ1 = ·∀ x τ1} {t2 = t2} {τ2 = ·∀ x' τ2} {ΓL} {ΓR} wf (AlphaForall alpha) with natEQ t1 x | natEQ t2 x'
  ... | Inl refl | Inl refl = AlphaForall (alpha-rewrite-gamma (ctx-lshadow {x = t1} {y = t2} ΓL) (ctx-lshadow {x = t2} {y = t1} ΓR) alpha)
  ... | Inr neq | Inl refl rewrite lem-alpha-sub-forall-asym {τ = τ} {ΓL = ΓL} {ΓR = ΓR} (flip neq) (alpha-rewrite-gamma refl (ctx-lshadow {x = t2} {y = x} ΓR) alpha) = 
            AlphaForall (lem-alpha-prunel1 ΓL ΓR x x' t1 (alpha-rewrite-gamma refl (ctx-lshadow {x = x'} {y = x} {z = t1} ΓR) alpha))
  ... | Inl refl | Inr neq rewrite lem-alpha-sub-forall-asym {τ = τ} {ΓL = ΓR} {ΓR = ΓL} (flip neq) (alpha-rewrite-gamma refl (ctx-lshadow {x = t1} {y = x'} ΓL) (alpha-sym-ctx ((■ (t1 , x')) ∪ ((■ (t1 , t2)) ∪ ΓL)) ((■ (x' , t1)) ∪ ((■ (t2 , t1)) ∪ ΓR)) τ1 τ2 alpha)) =
            AlphaForall (lem-alpha-pruner1 ΓL ΓR x x' t2 (alpha-rewrite-gamma (ctx-lshadow {x = t1} {y = x'} {z = t2} ΓL) refl alpha))
  ... | Inr neq | Inr neq' rewrite natEQneq (flip neq) rewrite natEQneq (flip neq') = AlphaForall (⊢alpha-sub {ΓL = ((■ (x , x')) ∪ ΓL)} {ΓR = ((■ (x' , x)) ∪ ΓR)} wf
    (alpha-rewrite-gamma (ctx-lextend-exchange {x = t1} {x' = t2} {y = x} {y' = x'} ΓL neq) (ctx-lextend-exchange {x = t2} {x' = t1} {y = x'} {y' = x} ΓR neq') alpha))

  alpha-sub : ∀{τ t1 τ1 t2 τ2} → ∅ ⊢ τ wf → ·∀ t1 τ1 =α ·∀ t2 τ2 → (Typ[ τ / t1 ] τ1) =α (Typ[ τ / t2 ] τ2)
  alpha-sub wf (AlphaForall alpha) = ⊢alpha-sub wf alpha

  -- Logic here is basically the same as ⊢alpha-sub
  wf-consist-refl : ∀{ΓL ΓR Θ τ} → Θ ⊢ τ wf → ((t : Nat) → (t , <>) ∈ Θ → (t , t) ∈ ΓL × (t , t) ∈ ΓR) → ΓL , ΓR ⊢ τ ~ τ
  wf-consist-refl (WFVar {a = a} x) cond = ConsistVarBound (π1 (cond a x)) (π2 (cond a x))
  wf-consist-refl WFBase cond = ConsistBase
  wf-consist-refl WFHole cond = ConsistHole1
  wf-consist-refl (WFArr wf wf₁) cond = ConsistArr (wf-consist-refl wf cond) (wf-consist-refl wf₁ cond)
  wf-consist-refl {ΓL} {ΓR} {Θ = Θ} (WFForall {n = n} wf) cond = ConsistForall (wf-consist-refl wf (λ t₁ x → lem-extend-refl t₁ ΓL (λ t z → π1 (cond t z)) x , lem-extend-refl t₁ ΓR (λ t z → π2 (cond t z)) x))

  closed-consist-refl : ∀{ΓL ΓR τ} → ∅ ⊢ τ wf → ΓL , ΓR ⊢ τ ~ τ
  closed-consist-refl wf = wf-consist-refl wf λ t x → abort (somenotnone (! x))

  ⊢consist-sub : ∀{τ t1 τ1 t2 τ2 ΓL ΓR} → tunboundt-in t1 τ1 → tunboundt-in t2 τ2 → ∅ ⊢ τ wf → ((■ (t1 , t2)) ∪ ΓL) , (■ (t2 , t1)) ∪ ΓR ⊢ τ1 ~ τ2 → ΓL , ΓR ⊢ (Typ[ τ / t1 ] τ1) ~ (Typ[ τ / t2 ] τ2)
  ⊢consist-sub ub1 ub2 wf ConsistBase = ConsistBase
  ⊢consist-sub {t1 = t1} {τ1 = T x} {t2 = t2} {τ2 = T x'} ub1 ub2 wf (ConsistVarBound x₁ x₂) with natEQ t1 x | natEQ t2 x' 
  ... | Inr neq | Inr neq' = ConsistVarBound x₁ x₂
  ... | Inl refl | Inr neq = abort (neq (someinj x₁))
  ... | Inr neq | Inl refl = abort (neq (someinj x₂))
  ... | Inl refl | Inl refl = closed-consist-refl wf
  ⊢consist-sub {t1 = t1} {τ1 = T x} {t2 = t2} {τ2 = T .x} ub1 ub2 wf (ConsistVarFree x₁ x₂) with natEQ t1 x | natEQ t2 x
  ... | Inr neq | Inr neq' = ConsistVarFree x₁ x₂
  ... | _ | Inl refl = abort (somenotnone x₂)
  ... | Inl refl | _ = abort (somenotnone x₁)
  ⊢consist-sub ub1 ub2 wf ConsistHole1 = ConsistHole1
  ⊢consist-sub ub1 ub2 wf ConsistHole2 = ConsistHole2
  ⊢consist-sub (UBArr ub1 ub3) (UBArr ub2 ub4) wf (ConsistArr consis consis₁) = ConsistArr (⊢consist-sub ub1 ub2 wf consis) (⊢consist-sub ub3 ub4 wf consis₁)
  ⊢consist-sub {t1 = t1} {t2 = t2} {ΓL = ΓL} {ΓR = ΓR} (UBForall ne1 ub1) (UBForall ne2 ub2) wf (ConsistForall {x = t'} {y = t''} consis) with natEQ t1 t' | natEQ t2 t''
  ... | Inl refl | _ = abort (ne1 refl)
  ... | _ | Inl refl = abort (ne2 refl)
  ... | Inr neq | Inr neq' = ConsistForall (⊢consist-sub ub1 ub2 wf 
    (consist-rewrite-gamma (ctx-lextend-exchange ΓL ne1) (ctx-lextend-exchange ΓR ne2) consis))
  
  consist-sub : ∀{τ t1 τ1 t2 τ2} → ∅ ⊢ τ wf → tunboundt-in t1 τ1 → tunboundt-in t2 τ2 → ·∀ t1 τ1 ~ ·∀ t2 τ2 → (Typ[ τ / t1 ] τ1) ~ (Typ[ τ / t2 ] τ2)
  consist-sub wf ub1 ub2 (ConsistForall consis) = ⊢consist-sub ub1 ub2 wf consis

  lem-sub-ub : ∀{t t' τ τ''} → (τ' : htyp) → tunboundt-in t τ' → tunboundt-in t τ'' → Typ[ τ'' / t' ] τ' == τ → tunboundt-in t τ
  lem-sub-ub b ub1 ub2 eq rewrite ! eq = ub1
  lem-sub-ub {t' = t'} (T x) ub1 ub2 eq with natEQ t' x
  ... | Inl refl rewrite eq = ub2
  ... | Inr neq rewrite ! eq = ub1
  lem-sub-ub ⦇-⦈ ub1 ub2 eq rewrite ! eq = ub1
  lem-sub-ub (τ' ==> τ'') (UBArr ub1 ub3) ub2 eq rewrite ! eq = UBArr (lem-sub-ub τ' ub1 ub2 refl) (lem-sub-ub τ'' ub3 ub2 refl)
  lem-sub-ub {t' = t'} (·∀ x τ') (UBForall ne ub1) ub2 eq with natEQ t' x
  ... | Inl refl rewrite ! eq = UBForall ne ub1
  ... | Inr neq rewrite ! eq = UBForall ne (lem-sub-ub τ' ub1 ub2 refl)

  lem-sub-sub-ub : ∀{t τ θ} → (τ' : htyp) → tunboundt-in t τ' → tunbound-in-θ t θ → apply-typenv θ τ' == τ → tunboundt-in t τ
  lem-sub-sub-ub τ' ub UBθId eq rewrite eq = ub
  lem-sub-sub-ub τ' ub (UBθSubst {θ = θ} x ubth) eq = lem-sub-ub (apply-typenv θ τ') (lem-sub-sub-ub τ' ub ubth refl) x eq

  lem-ub-extend : ∀{x t τ Γ} → tunboundt-in t τ → tunbound-in-Γ t Γ → tunbound-in-Γ t (Γ ,, (x , τ))
  lem-ub-extend {x} {t} {τ} {Γ} ubt (UBΓ ubg) = UBΓ foo
    where
      foo : (x' : Nat) -> (τ' : htyp) -> (x' , τ') ∈ (Γ ,, (x , τ)) -> tunboundt-in t τ'
      foo x' τ' mem with ctxindirect Γ x'
      ... | Inl (τ'' , ing) rewrite ing rewrite ! (someinj mem) = ubg x' τ'' ing
      ... | Inr nig rewrite nig with natEQ x x'
      ...   | Inl refl rewrite someinj mem = ubt
      ...   | Inr neq = abort (somenotnone (! mem))
  
  tunbound-ta-tunboundt : ∀{Δ Θ Γ d t τ} → tunbound-in t d → tunbound-in-Δ t Δ → tunbound-in-Γ t Γ → Δ , Θ , Γ ⊢ d :: τ → tunboundt-in t τ
  tunbound-ta-tunboundt ub ubd ubg TAConst = UBBase
  tunbound-ta-tunboundt {τ = τ} TUBVar ubd (UBΓ ubg) (TAVar {x = y} x) = ubg y τ x
  tunbound-ta-tunboundt (TUBLam2 ub ubt) ubd ubg (TALam x x₁ ta) = UBArr ubt (tunbound-ta-tunboundt ub ubd (lem-ub-extend ubt ubg) ta)
  tunbound-ta-tunboundt (TUBTLam x₁ ub) ubd ubg (TATLam x ta) = UBForall x₁ (tunbound-ta-tunboundt ub ubd ubg ta)
  tunbound-ta-tunboundt (TUBAp ub1 ub2) ubd ubg (TAAp ta ta₁ alpha) with tunbound-ta-tunboundt ub1 ubd ubg ta
  ... | UBArr _ ubt2 = ubt2
  tunbound-ta-tunboundt (TUBTAp ub ubt) ubd ubg (TATAp x ta eq) with tunbound-ta-tunboundt ub ubd ubg ta
  ... | UBForall ub' ubt' = lem-sub-ub _ ubt' ubt eq
  tunbound-ta-tunboundt (TUBHole ubt ubs) (UBΔ ubd) ubg (TAEHole {u = u} {Θ' = Θ'} {Γ' = Γ'} {τ' = τ'} x x₁ x₂ x₃) = let ubt' = ubd u Θ' Γ' τ' x in
    lem-sub-sub-ub τ' ubt' ubt (! x₂)
  tunbound-ta-tunboundt (TUBNEHole ubt ubs ub) (UBΔ ubd) ubg (TANEHole {u = u} {Θ' = Θ'} {Γ' = Γ'} {τ' = τ'} x ta x₁ x₂ x₃) = let ubt' = ubd u Θ' Γ' τ' x in
    lem-sub-sub-ub τ' ubt' ubt (! x₂)
  tunbound-ta-tunboundt (TUBCast ub ubt1 ubt2) ubd ubg (TACast ta x x₁ alpha) = ubt2
  tunbound-ta-tunboundt (TUBFailedCast ub ubt1 ubt2) ubd ubg (TAFailedCast ta x x₁ x₂ _) = ubt2
 