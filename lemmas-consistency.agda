open import Prelude
open import core
open import Nat

module lemmas-consistency where

  open typctx

  ~refl : {t : htyp} → t ~ t
  ~refl {b} = TCBase
  ~refl {⦇-⦈} = TCHole1
  ~refl {(t1 ==> t2)} = TCArr ~refl ~refl
  ~refl {(T p)} = TCVar 
  ~refl {(·∀ t1)} = TCForall ~refl

  -- ⊢~sym : {Γ : typctx} {t1 t2 : htyp} → Γ ⊢ t1 ~ t2 → Γ ⊢ t2 ~ t1
  -- ⊢~sym TCBase = TCBase
  -- ⊢~sym TCHole1 = TCHole2
  -- ⊢~sym TCHole2 = TCHole1
  -- ⊢~sym (TCArr p1 p2) = TCArr (⊢~sym p1) (⊢~sym p2)
  -- ⊢~sym (TCVar p) = TCVar p
  -- ⊢~sym (TCForall p) = TCForall (⊢~sym p)
  
  -- -- case for empty context
  -- ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  -- ~sym = ⊢~sym

  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym TCBase = TCBase
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)
  ~sym (TCVar) = TCVar
  ~sym (TCForall p) = TCForall (~sym p)

  -- type substitution preserves consistency
  ~Typ[] : {t1 t2 t : htyp} {n : Nat} → t1 ~ t2 → Typ[ t / n ] t1 ~ Typ[ t / n ] t2
  ~Typ[] TCBase = TCBase
  ~Typ[] TCHole1 = TCHole1
  ~Typ[] TCHole2 = TCHole2
  ~Typ[] {n = a} (TCVar {a = a'}) with natEQ a a'
  ... | Inl Refl = ~refl
  ... | Inr ne = ~refl
  ~Typ[] (TCArr x x') = TCArr (~Typ[] x) (~Typ[] x')
  ~Typ[] (TCForall x) = TCForall (~Typ[] x)
  
  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇-⦈ b TCHole1 TCHole2
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
  ~dec : (t1 t2 : htyp) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇-⦈ = Inl TCHole1
  ~dec ⦇-⦈ _ = Inl TCHole2
    -- num cases
  ~dec b b = Inl TCBase
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (\{(TCArr l r) -> y r})
  ... | Inr x | _     = Inr (\{(TCArr l r) -> x l})
  ~dec (T x) (T y) with natEQ x y
  ... | Inl refl = Inl TCVar 
  ... | Inr p = Inr \{(TCVar {a}) -> p refl}
  ~dec (·∀ t1) (·∀ t2) with ~dec t1 t2
  ... | Inl p = Inl (TCForall p)
  ... | Inr p = Inr (\{(TCForall p') -> p p'})
    -- cases with mismatched constructors
  ~dec b (T x) = Inr (λ ())
  ~dec b (t1 ==> t2) = Inr (λ ())
  ~dec b (·∀ t1) = Inr (λ ())
  ~dec (t1 ==> t2) b = Inr (λ ())
  ~dec (t1 ==> t2) (T x) = Inr (λ ())
  ~dec (t1 ==> t2) (·∀ t3) = Inr (λ ())
  ~dec (T x) b = Inr (λ ())
  ~dec (T x) (t1 ==> t2) = Inr (λ ())
  ~dec (T x) (·∀ t1) = Inr (λ ())
  ~dec (·∀ t1) b = Inr (λ ())
  ~dec (·∀ t1) (t2 ==> t3) = Inr (λ ())
  ~dec (·∀ t1) (T x) = Inr (λ ())

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : htyp} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  -- By definition
  ~apart x y = x y
