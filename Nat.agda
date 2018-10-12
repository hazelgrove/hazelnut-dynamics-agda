open import Prelude

module Nat where
  data Nat : Set where
    Z : Nat
    1+ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  -- the succ operation is injective
  1+inj : (x y : Nat) → (1+ x == 1+ y) → x == y
  1+inj Z .0 refl = refl
  1+inj (1+ x) .(1+ x) refl = refl

  1+notZ : (x : Nat) → 1+ x ≠ Z
  1+notZ Z = λ ()
  1+notZ (1+ x) = λ ()

  1+not2+ : (x : Nat) → 1+ (1+ x) ≠ 1+ x
  1+not2+ Z ()
  1+not2+ (1+ x) ()

  -- equality of naturals is decidable. we represent this as computing a
  -- choice of units, with inl <> meaning that the naturals are indeed the
  -- same and inr <> that they are not.
  natEQ : (x y : Nat) → ((x == y) + ((x == y) → ⊥))
  natEQ Z Z = Inl refl
  natEQ Z (1+ y) = Inr (λ ())
  natEQ (1+ x) Z = Inr (λ ())
  natEQ (1+ x) (1+ y) with natEQ x y
  natEQ (1+ x) (1+ .x) | Inl refl = Inl refl
  ... | Inr b = Inr (λ x₁ → b (1+inj x y x₁))

  -- nat equality as a predicate. this saves some very repetative casing.
  natEQp : (x y : Nat) → Set
  natEQp x y with natEQ x y
  natEQp x .x | Inl refl = ⊥
  natEQp x y | Inr x₁ = ⊤

  -- there are plenty of nats
  different-nat : (x : Nat) → Σ[ y ∈ Nat ] (y ≠ x)
  different-nat Z = 1+ Z , (λ ())
  different-nat (1+ x) with different-nat x
  different-nat (1+ x) | π1 , π2 with natEQ π1 x
  different-nat (1+ x) | .x , π2 | Inl refl = abort (π2 refl)
  different-nat (1+ x) | π1 , π2 | Inr x₁ = Z , (λ ())

  different-nat2 : (x y : Nat) → Σ[ z ∈ Nat ](z ≠ y × z ≠ x)
  different-nat2 Z Z = 1+ Z , (λ ()) , (λ ())
  different-nat2 Z (1+ y) = (1+ (1+ y)) , 1+not2+ y , 1+notZ (1+ y)
  different-nat2 (1+ x) Z = 1+ (1+ x) , 1+notZ (1+ x) , 1+not2+ x
  different-nat2 (1+ x) (1+ y) with different-nat2 x y
  ... | z , ≠x , ≠y = 1+ z , (λ x₁ → ≠x (1+inj z y x₁)) , (λ x₁ → ≠y (1+inj z x x₁))
