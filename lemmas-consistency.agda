open import Prelude
open import core
open import Nat

module lemmas-consistency where

  open ~ctx

  -- type consistency with any context is symmetric
  ∋syml : {Γ : ~ctx} {a b a' b' : Nat} → (_,_~_ Γ a b) ∋ a' ~ b' → (_,_~_ Γ b a) ∋ a' ~ b'
  ∋syml p with p
  ... | H = HSym
  ... | HSym = H
  ... | T w = T w
  
  ∋symr : {Γ : ~ctx} {a b : Nat} → Γ ∋ a ~ b → Γ ∋ b ~ a
  ∋symr p with p
  ... | H = HSym
  ... | HSym = H
  ... | T {Γ} {a} {d} {a'} {d'} w = T {Γ} {d} {a} {a'} {d'} (∋symr w)
  
  ⊢~comm : {Γ : ~ctx} {a b a' b' : Nat} {t1 t2 : htyp} → (_,_~_ (_,_~_ Γ a b) a' b') ⊢ t1 ~ t2 → (_,_~_ (_,_~_ Γ a' b') a b) ⊢ t1 ~ t2
  ⊢~comm TCBase = TCBase
  ⊢~comm TCHole1 = TCHole1
  ⊢~comm TCHole2 = TCHole2
  ⊢~comm (TCArr p1 p2) = TCArr (⊢~comm p1) (⊢~comm p2)
  ⊢~comm (TCVar p) with p
  ... | H = TCVar (T H)
  ... | HSym = TCVar (T HSym)
  ... | T H = TCVar H
  ... | T HSym = TCVar HSym
  ... | T (T t) = TCVar (T (T t))
  ⊢~comm (TCForall p) = {!!}
  
  ⊢~lsym : {Γ : ~ctx} {a b : Nat} {t1 t2 : htyp} → (_,_~_ Γ a b) ⊢ t1 ~ t2 → (_,_~_ Γ b a) ⊢ t1 ~ t2
  ⊢~lsym TCBase = TCBase
  ⊢~lsym TCHole1 = TCHole1
  ⊢~lsym TCHole2 = TCHole2
  ⊢~lsym (TCArr p1 p2) = TCArr (⊢~lsym p1) (⊢~lsym p2)
  ⊢~lsym (TCVar p) with p
  ... | H = TCVar HSym
  ... | HSym = TCVar H
  ... | T {Γ} {a} {d} {a'} {d'} w = TCVar (T {Γ} {a} {d} {d'} {a'} w)
  ⊢~lsym (TCForall p) = TCForall (⊢~comm (⊢~lsym (⊢~comm p)))
  
  ⊢~rsym : {Γ : ~ctx} {t1 t2 : htyp} → Γ ⊢ t1 ~ t2 → Γ ⊢ t2 ~ t1
  ⊢~rsym TCBase = TCBase
  ⊢~rsym TCHole1 = TCHole2
  ⊢~rsym TCHole2 = TCHole1
  ⊢~rsym (TCArr p1 p2) = TCArr (⊢~rsym p1) (⊢~rsym p2)
  ⊢~rsym (TCVar p) = TCVar (∋symr p)
  ⊢~rsym (TCForall p) = TCForall (⊢~rsym (⊢~lsym p))
  
  -- case for empty context
  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym = ⊢~rsym

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇-⦈ b TCHole1 TCHole2
  ... | ()
  
  -- if we extend a context that doesn't contain something with something else, it still won't contain that thing.
  ~ctxextendne : {Γ : ~ctx} {a b a' b' : Nat} → (( a ≠ a' + b ≠ b' ) × ( b ≠ a' + a ≠ b' )) → ¬(Γ ∋ a' ~ b') → ¬((_,_~_ Γ a b) ∋ a' ~ b')
  ~ctxextendne h t p with h | p
  ... | ( (Inl h1) , _ ) | H = h1 refl
  ... | ( (Inr h1) , _ ) | H = h1 refl
  ... | ( _ , (Inl h2) ) | HSym = h2 refl
  ... | ( _ , (Inr h2) ) | HSym = h2 refl
  ... | _ | T p' = t p'
  
  -- Looking up in a consistency context is decidable
  ∋dec : (Γ : ~ctx) → (a b : Nat) → ((Γ ∋ a ~ b) + ¬(Γ ∋ a ~ b))
  ∋dec ~∅ x y = Inr (λ ())
  ∋dec (Γ , x ~ y) x' y' with ∋dec Γ x' y'
  ...                     | Inl t = Inl (T t)
  ...                     | Inr t with natEQ x x' | natEQ x y' | natEQ y y' | natEQ y x'
  ... | Inr ne1 | Inr ne2 | _ | _ = Inr (~ctxextendne ( (Inl ne1) , (Inr ne2) ) t)
  ... | Inr ne1 | _ | _ | Inr ne2 = Inr (~ctxextendne ( (Inl ne1) , (Inl ne2) ) t)
  ... | _ | Inr ne1 | Inr ne2 | _ = Inr (~ctxextendne ( (Inr ne2) , (Inr ne1) ) t)
  ... | _ | _ | Inr ne1 | Inr ne2 = Inr (~ctxextendne ( (Inr ne1) , (Inl ne2) ) t)
  ... | Inl refl | _ | Inl refl | _ = Inl H
  ... | _ | Inl refl | _ | Inl refl = Inl HSym
  
  --  every pair of types is either consistent or not consistent
  ~dec : {Γ : ~ctx} (t1 t2 : htyp) → ((Γ ⊢ t1 ~ t2) + (Γ ⊢ t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇-⦈ = Inl TCHole1
  ~dec ⦇-⦈ _ = Inl TCHole2
    -- num cases
  ~dec b b = Inl TCBase
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (\{(TCArr l r) -> y r})
  ... | Inr x | _     = Inr (\{(TCArr l r) -> x l})
  ~dec {Γ} (A x) (A y) with ∋dec Γ x y
  ... | Inl p = Inl (TCVar p)
  ... | Inr p = Inr (\{(TCVar p') -> p p'})
  ~dec {Γ} (·∀ x t1) (·∀ y t2) with ~dec {(_,_~_ Γ x y)} t1 t2
  ... | Inl p = Inl (TCForall p)
  ... | Inr p = Inr (\{(TCForall p') -> p p'})
    -- cases with mismatched constructors
  ~dec b (A x) = Inr (λ ())
  ~dec b (t2 ==> t3) = Inr (λ ())
  ~dec b (·∀ x t2) = Inr (λ ())
  ~dec (t1 ==> t2) b = Inr (λ ())
  ~dec (t1 ==> t2) (A x) = Inr (λ ())
  ~dec (t1 ==> t2) (·∀ x t3) = Inr (λ ())
  ~dec (A x) b = Inr (λ ())
  ~dec (A x) (t2 ==> t3) = Inr (λ ())
  ~dec (A x) (·∀ x₁ t2) = Inr (λ ())
  ~dec (·∀ x t1) b = Inr (λ ())
  ~dec (·∀ x t1) (t2 ==> t3) = Inr (λ ())
  ~dec (·∀ x t1) (A x₁) = Inr (λ ())

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : htyp} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  -- By definition
  ~apart x y = x y
