open import Prelude
open import core

module lemmas-consistency where
  -- type consistency is symmetric
  ~sym : {t1 t2 : τ̇} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : τ̇) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇⦈ b TCHole1 TCHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ~dec : (t1 t2 : τ̇) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇⦈ = Inl TCHole1
  ~dec ⦇⦈ _ = Inl TCHole2
    -- num cases
  ~dec b b = Inl TCRefl
  ~dec b (t2 ==> t3) = Inr ICBaseArr1
    -- arrow cases
  ~dec (t1 ==> t2) b = Inr ICBaseArr2
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (ICArr2 y)
  ... | Inr x | _     = Inr (ICArr1 x)

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : τ̇} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart ICBaseArr1 ()
  ~apart ICBaseArr2 ()
  ~apart (ICArr1 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr1 x) (TCArr y y₁) = ~apart x y
  ~apart (ICArr2 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr2 x) (TCArr y y₁) = ~apart x y₁
