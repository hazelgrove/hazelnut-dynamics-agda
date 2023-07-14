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
  
  data _<_ : Nat → Nat → Set where
    LTZ : ∀{n} -> Z < 1+ n
    LTS : ∀{n m} -> n < m -> 1+ n < 1+ m
  
  natLT : (n m : Nat) -> ((n < m) + ¬(n < m))
  natLT Z Z = Inr (λ ())
  natLT Z (1+ n) = Inl LTZ
  natLT (1+ n) Z = Inr (λ ())
  natLT (1+ n) (1+ m) with natLT n m
  ... | Inl p = Inl (LTS p)
  ... | Inr p = Inr (\{(LTS p') -> p p'})

  lt-ne : {x y : Nat} -> x < y -> (x == y) → ⊥
  lt-ne LTZ = \ ()
  lt-ne (LTS {n} {m} p) = \eq -> lt-ne p ((1+inj n m eq))

  lt-antisym : {x y : Nat} -> x < y -> y < x -> ⊥
  lt-antisym LTZ = λ ()
  lt-antisym (LTS p) (LTS p') = lt-antisym p p'

  lt-gtz : {x y : Nat} -> y < x -> Σ[ z ∈ Nat ] (x == 1+ z)
  lt-gtz (LTZ {n}) = n , refl
  lt-gtz (LTS {n} {m} p) = let p1 , p2 = lt-gtz p in 1+ p1 , foo p2
    where
      foo : {x y : Nat} -> x == y -> 1+ x == 1+ y
      foo eq rewrite eq = refl

  lt-trans : {x y z : Nat} -> x < y -> y < z -> x < z
  lt-trans LTZ (LTS _) = LTZ
  lt-trans (LTS p) (LTS p') = LTS (lt-trans p p')

