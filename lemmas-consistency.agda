open import Prelude
open import core
open import Nat

module lemmas-consistency where

  open typctx

  ⊢~sym : {Γ : typctx} {t1 t2 : htyp} → Γ ⊢ t1 ~ t2 → Γ ⊢ t2 ~ t1
  ⊢~sym TCBase = TCBase
  ⊢~sym TCHole1 = TCHole2
  ⊢~sym TCHole2 = TCHole1
  ⊢~sym (TCArr p1 p2) = TCArr (⊢~sym p1) (⊢~sym p2)
  ⊢~sym (TCVar p) = TCVar p
  ⊢~sym (TCForall p) = TCForall (⊢~sym p)
  
  -- case for empty context
  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym = ⊢~sym

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇-⦈ b TCHole1 TCHole2
  ... | ()
  
  --  every pair of types is either consistent or not consistent
  ~dec : {Γ : typctx} (t1 t2 : htyp) → ((Γ ⊢ t1 ~ t2) + (Γ ⊢ t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇-⦈ = Inl TCHole1
  ~dec ⦇-⦈ _ = Inl TCHole2
    -- num cases
  ~dec b b = Inl TCBase
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (\{(TCArr l r) -> y r})
  ... | Inr x | _     = Inr (\{(TCArr l r) -> x l})
  ~dec {Γ} (A x) (A y) with natEQ x y
  ... | Inl refl with natLT x (typctx.n Γ) 
  ...   | Inl p = Inl (TCVar p)
  ...   | Inr p = Inr (\{(TCVar p') -> p p'})
  ~dec {Γ} (A x) (A y) | Inr neq = Inr (\{(TCVar _) -> neq refl})
  ~dec {Γ} (·∀ t1) (·∀ t2) with ~dec {[ Γ newtyp]} t1 t2
  ... | Inl p = Inl (TCForall p)
  ... | Inr p = Inr (\{(TCForall p') -> p p'})
    -- cases with mismatched constructors
  ~dec b (A x) = Inr (λ ())
  ~dec b (t1 ==> t2) = {! Inr (λ ()) !}
  ~dec b (·∀ t1) = Inr (λ ())
  ~dec (t1 ==> t2) b = Inr (λ ())
  ~dec (t1 ==> t2) (A x) = Inr (λ ())
  ~dec (t1 ==> t2) (·∀ t3) = Inr (λ ())
  ~dec (A x) b = Inr (λ ())
  ~dec (A x) (t1 ==> t2) = Inr (λ ())
  ~dec (A x) (·∀ t1) = Inr (λ ())
  ~dec (·∀ t1) b = Inr (λ ())
  ~dec (·∀ t1) (t2 ==> t3) = Inr (λ ())
  ~dec (·∀ t1) (A x) = Inr (λ ())

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : htyp} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  -- By definition
  ~apart x y = x y
