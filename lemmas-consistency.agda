open import Prelude
open import core
open import Nat

module lemmas-consistency where

  -- type consistency with any context is symmetric
  ~ctxsym : {Γ : core.~ctx.~ctx} {t1 t2 : htyp} → Γ ⊢ t1 ~ t2 → Γ ⊢ t2 ~ t1
  ~ctxsym TCBase = TCBase
  ~ctxsym TCHole1 = TCHole2
  ~ctxsym TCHole2 = TCHole1
  ~ctxsym (TCArr p1 p2) = TCArr (~ctxsym p1) (~ctxsym p2)
  ~ctxsym (TCForall p) = TCForall (~ctxsym p)
  ~ctxsym (TCVar p) = TCVar p
  
  -- case for empty context
  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym = ~ctxsym

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇-⦈ b TCHole1 TCHole2
  ... | ()

  open ~ctx
  
  -- if we extend a context that doesn't contain something with something else, it still won't contain that thing.
  ~ctxextendne : (Γ : ~ctx) (a a' : Nat) → a ≠ a' → ¬(Γ ∋ a) → ¬((Γ , a') ∋ a)
  ~ctxextendne Γ a a' h t p with p
  ... | H = h refl
  ... | T p' = t p'
  
  -- Looking up in a consistency context is decidable
  ~Γdec : (Γ : ~ctx) → (a : Nat) → ((Γ ∋ a) + ¬(Γ ∋ a))
  ~Γdec ~∅ a = Inr (λ ())
  ~Γdec (Γ , a) a' with natEQ a' a | ~Γdec Γ a'
  ... | Inl refl | _ = Inl H
  ... | Inr neq | Inl x = Inl (T x)
  ... | Inr neq | Inr y = Inr (~ctxextendne Γ a' a neq y)
  
  --  every pair of types is either consistent or not consistent
  ~dec : (Γ : ~ctx) (t1 t2 : htyp) → ((Γ ⊢ t1 ~ t2) + (Γ ⊢ t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ _ ⦇-⦈ = Inl TCHole1
  ~dec _ ⦇-⦈ _ = Inl TCHole2
    -- num cases
  ~dec _ b b = Inl TCBase
  ~dec Γ (t1 ==> t2) (t3 ==> t4) with ~dec Γ t1 t3 | ~dec Γ t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (\{(TCArr l r) -> y r})
  ... | Inr x | _     = Inr (\{(TCArr l r) -> x l})
  ~dec _ _ _ = Inr (λ ())
  
{-
  ~dec _ b (t2 ==> t3) = Inr ICBaseArr1
    -- arrow cases
  ~dec _ (t1 ==> t2) b = Inr ICBaseArr2
  ~dec Γ (t1 ==> t2) (t3 ==> t4) with ~dec Γ t1 t3 | ~dec Γ t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (ICArr2 y)
  ... | Inr x | _     = Inr (ICArr1 x)
  ~dec Γ (A x) (A y) with natEQ x y | ~Γdec Γ x
  ... | Inl refl | Inl inenv = Inl (TCVar inenv)
  ... | Inl refl | Inr ninenv = Inr {!!}
  ... | Inr neq | _ = Inr (ICVar neq)
  ~dec _ b (A x) = Inr ICBaseVar1
  ~dec _ (A x) b = Inr ICBaseVar2
-}

{-
  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : htyp} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart ICBaseArr1 ()
  ~apart ICBaseArr2 ()
  ~apart (ICArr1 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr1 x) (TCArr y y₁) = ~apart x y
  ~apart (ICArr2 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr2 x) (TCArr y y₁) = ~apart x y₁
-}
