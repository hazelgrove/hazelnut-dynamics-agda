open import Prelude
open import core
open import contexts
open import Nat

module lemmas-consistency where

  open alpha

  ⊢~refl : {Γ : Nat ctx} -> {t : htyp} → (∀ {x y} → (x , y) ∈ Γ → (x , x) ∈ Γ) -> (_,_⊢_~_) Γ Γ t t
  ⊢~refl {t = b} _ = ConsistBase
  ⊢~refl {Γ} {t = T x} r with ctxindirect Γ x
  ... | Inr ning = ConsistVarFree ning ning
  ... | Inl (y , ing) rewrite ing = ConsistVarBound (r ing) (r ing)
  ⊢~refl {t = ⦇-⦈} _ = ConsistHole1
  ⊢~refl {t = t1 ==> t2} r = ConsistArr (⊢~refl r) (⊢~refl r)
  ⊢~refl {Γ = Γ} {t = ·∀ x t} r = ConsistForall (⊢~refl λ x' → reflex-extend {x = x} {Γ = Γ} r x')

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

  -- type substitution preserves consistency
  {-
  ⊢~Typ[] : {ΓL ΓR : Nat ctx} {t1 t2 t : htyp} {n : Nat} → ΓL , ΓR ⊢ t1 ~ t2 → ΓL , ΓR ⊢ Typ[ t / n ] t1 ~ Typ[ t / n ] t2
  ⊢~Typ[] ConsistBase = ConsistBase
  ⊢~Typ[] {n = n} (ConsistVarFree {x = x} l r) with natEQ n x
  ... | Inl refl = {!!}
  ... | Inr neq = {!~refl!}
  ⊢~Typ[] ConsistHole1 = ConsistHole1
  ⊢~Typ[] ConsistHole2 = ConsistHole2
  ⊢~Typ[] (ConsistArr p p₁) = ConsistArr (⊢~Typ[] p) (⊢~Typ[] p₁)
  ⊢~Typ[] (ConsistForall {x = x} {y = y} p) = {!   !}
  -}
  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇-⦈ b ConsistHole1 ConsistHole2
  ... | ()
  
  -- --  every pair of types is either consistent or not consistent
  -- ~dec : {Γ : typctx} (t1 t2 : htyp) → ((Γ ⊢ t1 ~ t2) + (Γ ⊢ t1 ~̸ t2))
  --   -- this takes care of all hole cases, so we don't consider them below
  -- ~dec _ ⦇-⦈ = Inl TCHole1
  -- ~dec ⦇-⦈ _ = Inl TCHole2
  --   -- num cases
  -- ~dec b b = Inl TCBase
  -- ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  -- ... | Inl x | Inl y = Inl (TCArr x y)
  -- ... | Inl _ | Inr y = Inr (\{(TCArr l r) -> y r})
  -- ... | Inr x | _     = Inr (\{(TCArr l r) -> x l})
  -- ~dec {Γ} (T x) (T y) with natEQ x y
  -- ... | Inl refl with natLT x (typctx.n Γ) 
  -- ...   | Inl p = Inl (TCVar p)
  -- ...   | Inr p = Inr (\{(TCVar p') -> p p'})
  -- ~dec {Γ} (T x) (T y) | Inr neq = Inr (\{(TCVar _) -> neq refl})
  -- ~dec {Γ} (·∀ t1) (·∀ t2) with ~dec {[ Γ newtyp]} t1 t2
  -- ... | Inl p = Inl (TCForall p)
  -- ... | Inr p = Inr (\{(TCForall p') -> p p'})
  --   -- cases with mismatched constructors
  -- ~dec b (T x) = Inr (λ ())
  -- ~dec b (t1 ==> t2) = Inr (λ ())
  -- ~dec b (·∀ t1) = Inr (λ ())
  -- ~dec (t1 ==> t2) b = Inr (λ ())
  -- ~dec (t1 ==> t2) (T x) = Inr (λ ())
  -- ~dec (t1 ==> t2) (·∀ t3) = Inr (λ ())
  -- ~dec (T x) b = Inr (λ ())
  -- ~dec (T x) (t1 ==> t2) = Inr (λ ())
  -- ~dec (T x) (·∀ t1) = Inr (λ ())
  -- ~dec (·∀ t1) b = Inr (λ ())
  -- ~dec (·∀ t1) (t2 ==> t3) = Inr (λ ())
  -- ~dec (·∀ t1) (T x) = Inr (λ ())

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

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : htyp} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  -- By definition
  ~apart x y = x y
  