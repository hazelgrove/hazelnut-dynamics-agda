open import Prelude
open import core

module lemmas-consistency where
  -- type consistency is symmetric
  ~sym : {t1 t2 : τ̇} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)
  ~sym (TCSum p1 p2) = TCSum (~sym p1) (~sym p2)
  ~sym (TCPro p1 p2) = TCPro (~sym p1) (~sym p2)

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : τ̇) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (num ==> num) ⦇⦈ num TCHole1 TCHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ~dec : (t1 t2 : τ̇) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇⦈ = Inl TCHole1
  ~dec ⦇⦈ _ = Inl TCHole2
    -- num cases
  ~dec num num = Inl TCRefl
  ~dec num (t2 ==> t3) = Inr ICNumArr1
    -- arrow cases
  ~dec (t1 ==> t2) num = Inr ICNumArr2
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (ICArr2 y)
  ... | Inr x | _     = Inr (ICArr1 x)
    -- plus cases
  ~dec (t1 ⊕ t2) num = Inr ICNumSum2
  ~dec (t1 ⊕ t2) (t3 ==> t4) = Inr ICSumArr1
  ~dec (t1 ⊕ t2) (t3 ⊕ t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCSum x y)
  ... | _     | Inr x = Inr (ICSum2 x)
  ... | Inr x | Inl _ = Inr (ICSum1 x)
  ~dec num (y ⊕ y₁) = Inr ICNumSum1
  ~dec (x ==> x₁) (y ⊕ y₁) = Inr ICSumArr2
  ~dec num (t2 ⊗ t3) = Inr ICNumPro1
  ~dec (t1 ==> t2) (t3 ⊗ t4) = Inr ICProArr2
  ~dec (t1 ⊕ t2) (t3 ⊗ t4) = Inr ICProSum2
  ~dec (t1 ⊗ t2) num = Inr ICNumPro2
  ~dec (t1 ⊗ t2) (t3 ==> t4) = Inr ICProArr1
  ~dec (t1 ⊗ t2) (t3 ⊕ t4) = Inr ICProSum1
  ~dec (t1 ⊗ t2) (t3 ⊗ t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCPro x y)
  ... | _     | Inr x = Inr (ICPro2 x)
  ... | Inr x | Inl _ = Inr (ICPro1 x)

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : τ̇} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart ICNumArr1 ()
  ~apart ICNumArr2 ()
  ~apart (ICArr1 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr1 x) (TCArr y y₁) = ~apart x y
  ~apart (ICArr2 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr2 x) (TCArr y y₁) = ~apart x y₁
  ~apart ICNumSum1 ()
  ~apart ICNumSum2 ()
  ~apart (ICSum1 x) TCRefl = ~apart x TCRefl
  ~apart (ICSum1 x) (TCSum y y₁) = ~apart x y
  ~apart (ICSum2 x) TCRefl = ~apart x TCRefl
  ~apart (ICSum2 x) (TCSum y y₁) = ~apart x y₁
  ~apart ICSumArr1 ()
  ~apart ICSumArr2 ()
  ~apart ICNumPro1 ()
  ~apart ICNumPro2 ()
  ~apart (ICPro1 x) TCRefl = ~apart x TCRefl
  ~apart (ICPro1 x) (TCPro y y₁) = ~apart x y
  ~apart (ICPro2 x) TCRefl = ~apart x TCRefl
  ~apart (ICPro2 x) (TCPro y y₁) = ~apart x y₁
  ~apart ICProArr1 ()
  ~apart ICProArr2 ()
  ~apart ICProSum1 ()
  ~apart ICProSum2 ()
