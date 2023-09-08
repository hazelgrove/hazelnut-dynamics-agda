open import Prelude
open import core
open import contexts
open import Nat
open import lemmas-alpha -- For reflex-extend

module lemmas-consistency where

  open alpha

  ⊢~refl : {Γ : Nat ctx} -> {t : htyp} → (∀ {x y} → (x , y) ∈ Γ → (x , x) ∈ Γ) -> Γ , Γ ⊢ t ~ t
  ⊢~refl {t = b} _ = ConsistBase
  ⊢~refl {Γ} {t = T x} r with ctxindirect Γ x
  ... | Inr ning = ConsistVarFree ning ning
  ... | Inl (y , ing) rewrite ing = ConsistVarBound (r ing) (r ing)
  ⊢~refl {t = ⦇-⦈} _ = ConsistHole1
  ⊢~refl {t = t1 ==> t2} r = ConsistArr (⊢~refl r) (⊢~refl r)
  ⊢~refl {Γ = Γ} {t = ·∀ x t} r = ConsistForall (⊢~refl λ x' → reflex-extend x r x')

  ~refl : {t : htyp} -> t ~ t
  ~refl = ⊢~refl (λ ())

  ⊢~sym : {ΓL ΓR : Nat ctx} -> {t1 t2 : htyp} → ΓL , ΓR ⊢ t1 ~ t2 → ΓR , ΓL ⊢ t2 ~ t1
  ⊢~sym ConsistBase = ConsistBase
  ⊢~sym (ConsistVarBound x x₁) = ConsistVarBound x₁ x
  ⊢~sym (ConsistVarFree x x₁) = ConsistVarFree x₁ x
  ⊢~sym ConsistHole1 = ConsistHole2
  ⊢~sym ConsistHole2 = ConsistHole1
  ⊢~sym (ConsistArr p p₁) = ConsistArr (⊢~sym p) (⊢~sym p₁)
  ⊢~sym (ConsistForall p) = ConsistForall (⊢~sym p)

  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym = ⊢~sym

  --  every pair of types is either consistent or not consistent
  ⊢alpha-dec : {ΓL ΓR : Nat ctx} -> (t1 t2 : htyp) → ((ΓL , ΓR ⊢ t1 =α t2) + ¬(ΓL , ΓR ⊢ t1 =α t2))
    -- this takes care of all hole cases, so we don't consider them below
  ⊢alpha-dec ⦇-⦈ ⦇-⦈ = Inl AlphaHole
    -- num cases
  ⊢alpha-dec b b = Inl AlphaBase
  ⊢alpha-dec (t1 ==> t2) (t3 ==> t4) with ⊢alpha-dec t1 t3 | ⊢alpha-dec t2 t4
  ... | Inl x | Inl y = Inl (AlphaArr x y)
  ... | Inl _ | Inr y = Inr (\{(AlphaArr l r) -> y r})
  ... | Inr x | _     = Inr (\{(AlphaArr l r) -> x l})
  ⊢alpha-dec {ΓL} {ΓR} (T x) (T y) with ctxindirect ΓL x | ctxindirect ΓR y
  ... | Inl (xbind , ingl) | Inr ningr = Inr (λ{(AlphaVarBound l r) -> abort (somenotnone ((! r) · ningr)) ; (AlphaVarFree l r) → abort (somenotnone ((! ingl) · l))})
  ... | Inr ningl | Inl (ybind , ingr) = Inr (λ{(AlphaVarBound l r) -> abort (somenotnone ((! l) · ningl)) ; (AlphaVarFree l r) → abort (somenotnone ((! ingr) · r))})
  ... | Inr ningl | Inr ningr with natEQ x y
  ...   | Inl refl = Inl (AlphaVarFree ningl ningr)
  ...   | Inr neq = Inr (λ{(AlphaVarBound l r) -> abort (somenotnone ((! l) · ningl)) ; (AlphaVarFree l r) → neq refl})
  ⊢alpha-dec {ΓL} {ΓR} (T x) (T y) | Inl (xbind , ingl) | Inl (ybind , ingr) with natEQ xbind y | natEQ ybind x
  ...   | Inl refl | Inl refl = Inl (AlphaVarBound ingl ingr) 
  ...   | Inr neq | _ rewrite ingl rewrite ingr = Inr (λ {(AlphaVarBound l r) → neq (someinj ((! ingl) · l)) ; (AlphaVarFree l r) -> abort (somenotnone ((! ingl) · l))})
  ...   | Inl refl | Inr neq rewrite ingl rewrite ingr = Inr (λ {(AlphaVarBound l r) → neq (someinj ((! ingr) · r)); (AlphaVarFree l r) -> abort (somenotnone ((! ingr) · r))})
  -- ... | Inr p = Inr (\{(AlphaVarBound l r) -> {! abort (somenotnone (! r)) !} ; (AlphaVarFree l r) -> p refl})
  ⊢alpha-dec {ΓL} {ΓR} (·∀ n1 t1) (·∀ n2 t2) with ⊢alpha-dec {(■ (n1 , n2) ∪ ΓL)} {(■ (n2 , n1) ∪ ΓR)} t1 t2
  ... | Inl yes = Inl (AlphaForall yes)
  ... | Inr no = Inr (λ {(AlphaForall x) → no x})
    -- cases with mismatched constructors
  ⊢alpha-dec b ⦇-⦈ = Inr (λ ())
  ⊢alpha-dec b (T x) = Inr (λ ())
  ⊢alpha-dec b (t1 ==> t2) = Inr (λ ())
  ⊢alpha-dec b (·∀ _ t1) = Inr (λ ())
  ⊢alpha-dec (t1 ==> t2) ⦇-⦈ = Inr (λ ())
  ⊢alpha-dec (t1 ==> t2) b = Inr (λ ())
  ⊢alpha-dec (t1 ==> t2) (T x) = Inr (λ ())
  ⊢alpha-dec (t1 ==> t2) (·∀ _ t3) = Inr (λ ())
  ⊢alpha-dec (T x) ⦇-⦈ = Inr (λ ())
  ⊢alpha-dec (T x) b = Inr (λ ())
  ⊢alpha-dec (T x) (t1 ==> t2) = Inr (λ ())
  ⊢alpha-dec (T x) (·∀ _ t1) = Inr (λ ())
  ⊢alpha-dec (·∀ _ t1) ⦇-⦈ = Inr (λ ())
  ⊢alpha-dec (·∀ _ t1) b = Inr (λ ())
  ⊢alpha-dec (·∀ _ t1) (t2 ==> t3) = Inr (λ ())
  ⊢alpha-dec (·∀ _ t1) (T x) = Inr (λ ())
  ⊢alpha-dec ⦇-⦈ b = Inr (λ ())
  ⊢alpha-dec ⦇-⦈ (t2 ==> t3) = Inr (λ ())
  ⊢alpha-dec ⦇-⦈ (T x) = Inr (λ ())
  ⊢alpha-dec ⦇-⦈ (·∀ _ t1) = Inr (λ ())

  alpha-dec : (t1 t2 : htyp) → ((t1 =α t2) + ¬(t1 =α t2))
  alpha-dec = ⊢alpha-dec

  ground-alpha-ground : ∀ {t1 t2} → (t1 ground) → (t1 =α t2) → (t2 ground)
  ground-alpha-ground GBase AlphaBase = GBase
  ground-alpha-ground GArr (AlphaArr AlphaHole AlphaHole) = GArr
  ground-alpha-ground GForall (AlphaForall AlphaHole) = GForall

  -- type substitution preserves consistency
  -- I think we need something stronger, like apartness of free variables in t1, t2 and t or something.
  {-
  ⊢~Typ[] : {ΓL ΓR : Nat ctx} {t1 t2 t : htyp} {n : Nat} → tbinderstt-disjoint t1 t -> tbinderstt-disjoint t2 t -> ΓL , ΓR ⊢ t ~ t -> ΓL , ΓR ⊢ t1 ~ t2 → ΓL , ΓR ⊢ Typ[ t / n ] t1 ~ Typ[ t / n ] t2
  ⊢~Typ[] _ _ _ ConsistBase = ConsistBase
  ⊢~Typ[] {n = n} bdl bdr ~t (ConsistVarFree {x = x} l r) with natEQ n x
  ... | Inl refl = ~t
  ... | Inr neq = ConsistVarFree l r
  ⊢~Typ[] {n = n} bdl bdr ~t (ConsistVarBound {x = x} {y = y} l r) with natEQ n x | natEQ n y 
  ... | Inl refl | Inl refl = ~t
  ⊢~Typ[] {n = n} BDTTVar BDTTVar ~t (ConsistVarBound {x = _} {_} l r) | Inr neq | Inl refl = {!   !}
  ... | Inr neq | Inr neq' = {!!}
  ⊢~Typ[] _ _ _ ConsistHole1 = ConsistHole1
  ⊢~Typ[] _ _ _ ConsistHole2 = ConsistHole2
  ⊢~Typ[] (BDTArr bdl1 bdl2) (BDTArr bdr1 bdr2) ~t (ConsistArr p p₁) = ConsistArr {!   !}  {!   !} -- ConsistArr {! (⊢~Typ[] p) (⊢~Typ[] p₁) !}
  ⊢~Typ[] {n = n} bdl bdr ~t (ConsistForall {x = x} {y = y} p) with natEQ n x | natEQ n y 
  ... | Inl refl | Inl refl = ConsistForall {!   !}
  ... | Inl refl | Inr neq = {! !}
  ... | Inr neq | Inr neq' = {!!}
  -}

  wf⊢~refl : {ΓL ΓR : Nat ctx} {Θ : typctx} {τ : htyp} → Θ ⊢ τ wf → ((t : Nat) → (t , <>) ∈ Θ → ((t , t) ∈ ΓL × (t , t) ∈ ΓR)) → ΓL , ΓR ⊢ τ ~ τ
  wf⊢~refl (WFVar {a = a} x) cond = ConsistVarBound (π1 (cond a x)) (π2 (cond a x))
  wf⊢~refl WFBase cond = ConsistBase
  wf⊢~refl WFHole cond = ConsistHole1
  wf⊢~refl (WFArr wf wf₁) cond = ConsistArr (wf⊢~refl wf cond) (wf⊢~refl wf₁ cond)
  wf⊢~refl {ΓL} {ΓR} {Θ} {τ} (WFForall {n = n} wf) cond = ConsistForall (wf⊢~refl wf foo)
    where
      foo : (t : Nat) -> (t , <>) ∈ (Θ ,, (n , <>)) -> ((t , t) ∈ ((■ (n , n)) ∪ ΓL)) × ((t , t) ∈ ((■ (n , n)) ∪ ΓR))
      foo t mem with natEQ n t
      ... | Inl refl = refl , refl
      ... | Inr neq with ctxindirect Θ t
      ...   | Inl (<> , int) rewrite int rewrite natEQneq neq = cond t int
      ...   | Inr nit rewrite nit rewrite natEQneq neq = abort (somenotnone (! mem))


  closed-~refl : {ΓL ΓR : Nat ctx} {τ : htyp} → ∅ ⊢ τ wf → ΓL , ΓR ⊢ τ ~ τ
  closed-~refl wf = wf⊢~refl wf λ t x → abort (somenotnone (! x))

  ⊢~Typ[] : {ΓL ΓR : Nat ctx} {t1 t2 t : htyp} {n : Nat} → ∅ ⊢ t wf -> n # ΓL -> n # ΓR -> tunboundt-in n t1 -> tunboundt-in n t2 -> ΓL , ΓR ⊢ t ~ t -> ΓL , ΓR ⊢ t1 ~ t2 → ΓL , ΓR ⊢ Typ[ t / n ] t1 ~ Typ[ t / n ] t2
  ⊢~Typ[] wf aptl aptr ub1 ub2 ih ConsistBase = ConsistBase
  ⊢~Typ[] {n = n} wf aptl aptr ub1 ub2 ih (ConsistVarBound {x = x} {y = y} inl inr) with natEQ n x | natEQ n y
  ... | Inl refl | _ = abort (somenotnone ((! inl) · aptl))
  ... | _ | Inl refl = abort (somenotnone ((! inr) · aptr))
  ... | Inr neq1 | Inr neq2 = ConsistVarBound inl inr
  ⊢~Typ[] {n = n} wf aptl aptr ub1 ub2 ih (ConsistVarFree {x = x} nil nir) with natEQ n x 
  ... | Inl refl = ih
  ... | Inr neq = ConsistVarFree nil nir
  ⊢~Typ[] wf aptl aptr ub1 ub2 ih ConsistHole1 = ConsistHole1
  ⊢~Typ[] wf aptl aptr ub1 ub2 ih ConsistHole2 = ConsistHole2
  ⊢~Typ[] wf aptl aptr (UBArr ub1 ub1') (UBArr ub2 ub2') ih (ConsistArr consist1 consist2) = ConsistArr (⊢~Typ[] wf aptl aptr ub1 ub2 ih consist1) (⊢~Typ[] wf aptl aptr ub1' ub2' ih consist2)
  ⊢~Typ[] wf aptl aptr (UBForall neq1 ub1) (UBForall neq2 ub2) ih (ConsistForall consist) rewrite natEQneq neq1 rewrite natEQneq neq2 = 
    ConsistForall (⊢~Typ[] wf (lem-apart-extend-rev aptl neq1) (lem-apart-extend-rev aptr neq2) ub1 ub2 (closed-~refl wf) consist)

  ~Typ[] : {t1 t2 t : htyp} {n : Nat} → ∅ ⊢ t wf -> tunboundt-in n t1 -> tunboundt-in n t2 -> t1 ~ t2 → Typ[ t / n ] t1 ~ Typ[ t / n ] t2
  ~Typ[] wf ub1 ub2 consist = ⊢~Typ[] wf refl refl ub1 ub2 ~refl consist

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇-⦈ b ConsistHole1 ConsistHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ⊢~dec : {ΓL ΓR : Nat ctx} -> (t1 t2 : htyp) → ((ΓL , ΓR ⊢ t1 ~ t2) + ¬(ΓL , ΓR ⊢ t1 ~ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ⊢~dec _ ⦇-⦈ = Inl ConsistHole1
  ⊢~dec ⦇-⦈ _ = Inl ConsistHole2
    -- num cases
  ⊢~dec b b = Inl ConsistBase
  ⊢~dec (t1 ==> t2) (t3 ==> t4) with ⊢~dec t1 t3 | ⊢~dec t2 t4
  ... | Inl x | Inl y = Inl (ConsistArr x y)
  ... | Inl _ | Inr y = Inr (\{(ConsistArr l r) -> y r})
  ... | Inr x | _     = Inr (\{(ConsistArr l r) -> x l})
  ⊢~dec {ΓL} {ΓR} (T x) (T y) with ctxindirect ΓL x | ctxindirect ΓR y
  ... | Inl (xbind , ingl) | Inr ningr = Inr (λ{(ConsistVarBound l r) -> abort (somenotnone ((! r) · ningr)) ; (ConsistVarFree l r) → abort (somenotnone ((! ingl) · l))})
  ... | Inr ningl | Inl (ybind , ingr) = Inr (λ{(ConsistVarBound l r) -> abort (somenotnone ((! l) · ningl)) ; (ConsistVarFree l r) → abort (somenotnone ((! ingr) · r))})
  ... | Inr ningl | Inr ningr with natEQ x y
  ...   | Inl refl = Inl (ConsistVarFree ningl ningr)
  ...   | Inr neq = Inr (λ{(ConsistVarBound l r) -> abort (somenotnone ((! l) · ningl)) ; (ConsistVarFree l r) → neq refl})
  ⊢~dec {ΓL} {ΓR} (T x) (T y) | Inl (xbind , ingl) | Inl (ybind , ingr) with natEQ xbind y | natEQ ybind x
  ...   | Inl refl | Inl refl = Inl (ConsistVarBound ingl ingr) 
  ...   | Inr neq | _ rewrite ingl rewrite ingr = Inr (λ {(ConsistVarBound l r) → neq (someinj ((! ingl) · l)) ; (ConsistVarFree l r) -> abort (somenotnone ((! ingl) · l))})
  ...   | Inl refl | Inr neq rewrite ingl rewrite ingr = Inr (λ {(ConsistVarBound l r) → neq (someinj ((! ingr) · r)); (ConsistVarFree l r) -> abort (somenotnone ((! ingr) · r))})
  -- ... | Inr p = Inr (\{(ConsistVarBound l r) -> {! abort (somenotnone (! r)) !} ; (ConsistVarFree l r) -> p refl})
  ⊢~dec {ΓL} {ΓR} (·∀ n1 t1) (·∀ n2 t2) with ⊢~dec {(■ (n1 , n2) ∪ ΓL)} {(■ (n2 , n1) ∪ ΓR)} t1 t2
  ... | Inl yes = Inl (ConsistForall yes)
  ... | Inr no = Inr (λ {(ConsistForall x) → no x})
    -- cases with mismatched constructors
  ⊢~dec b (T x) = Inr (λ ())
  ⊢~dec b (t1 ==> t2) = Inr (λ ())
  ⊢~dec b (·∀ _ t1) = Inr (λ ())
  ⊢~dec (t1 ==> t2) b = Inr (λ ())
  ⊢~dec (t1 ==> t2) (T x) = Inr (λ ())
  ⊢~dec (t1 ==> t2) (·∀ _ t3) = Inr (λ ())
  ⊢~dec (T x) b = Inr (λ ())
  ⊢~dec (T x) (t1 ==> t2) = Inr (λ ())
  ⊢~dec (T x) (·∀ _ t1) = Inr (λ ())
  ⊢~dec (·∀ _ t1) b = Inr (λ ())
  ⊢~dec (·∀ _ t1) (t2 ==> t3) = Inr (λ ())
  ⊢~dec (·∀ _ t1) (T x) = Inr (λ ())

  ~dec : (t1 t2 : htyp) → ((t1 ~ t2) + ¬(t1 ~ t2))
  ~dec = ⊢~dec

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : htyp} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  -- By definition
  ~apart x y = x y
  
  alpha-~-ctx : ∀ {ΓL ΓR t1 t2} → (ΓL , ΓR ⊢ t1 =α t2) → (ΓL , ΓR ⊢ t1 ~ t2)
  alpha-~-ctx AlphaBase = ConsistBase
  alpha-~-ctx (AlphaVarBound x x₁) = ConsistVarBound x x₁
  alpha-~-ctx (AlphaVarFree x x₁) = ConsistVarFree x x₁
  alpha-~-ctx AlphaHole = ConsistHole1
  alpha-~-ctx (AlphaArr eq eq₁) = ConsistArr (alpha-~-ctx eq) (alpha-~-ctx eq₁)
  alpha-~-ctx (AlphaForall eq) = ConsistForall (alpha-~-ctx eq)

  alpha-~ : ∀ {t1 t2} → (t1 =α t2) → (t1 ~ t2)
  alpha-~ eq = alpha-~-ctx eq

  ground-eq-~ : ∀ {t1 t2} → (t1 ground) → (t2 ground) → (t1 ~ t2) → (t1 =α t2)
  ground-eq-~ GBase GBase con = AlphaBase
  ground-eq-~ GArr GArr con = AlphaArr AlphaHole AlphaHole
  ground-eq-~ GForall GForall con = AlphaForall AlphaHole
