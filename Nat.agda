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

  natEQrefl : {x : Nat} -> natEQ x x == Inl refl
  natEQrefl {x} with natEQ x x
  ... | Inl refl = refl
  ... | Inr neq = abort (neq refl)

  natEQneq : {x y : Nat} -> (neq : ((x == y) → ⊥)) -> natEQ x y == Inr neq
  natEQneq {x} {y} neq with natEQ x y
  ... | Inl refl = abort (neq refl)
  ... | Inr neq' = inr-inj (funext (λ eq → abort (neq eq)))
    where
      inr-inj : ∀{a a'} -> a == a' -> Inr a == Inr a'
      inr-inj eq rewrite eq = refl

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

  lt-1+ : {x : Nat} -> x < 1+ x
  lt-1+ {Z} = LTZ
  lt-1+ {1+ x'} = LTS lt-1+

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

  lt-1+-inj : {x y : Nat} -> 1+ x < 1+ y -> x < y
  lt-1+-inj (LTS p) = p
  
  lt-trans-1+ : {x y z : Nat} -> x < y -> y < z -> 1+ x < z
  lt-trans-1+ LTZ (LTS LTZ) = LTS LTZ
  lt-trans-1+ LTZ (LTS (LTS p)) = LTS LTZ
  lt-trans-1+ (LTS p) (LTS p') = LTS (lt-trans-1+ p p')

  lt-right-incr : {x y : Nat} -> x < y -> x < 1+ y
  lt-right-incr LTZ = LTZ
  lt-right-incr (LTS p) = LTS (lt-right-incr p)
      
  lt-trans : {x y z : Nat} -> x < y -> y < z -> x < z
  lt-trans LTZ (LTS p) = LTZ
  lt-trans (LTS p) (LTS p') = lt-right-incr (lt-trans-1+ p p')

  lt-right-incr-neq : {x y : Nat} -> x < 1+ y -> ((x == y) -> ⊥) -> x < y
  lt-right-incr-neq {y = 0} LTZ d = abort (d refl)
  lt-right-incr-neq {y = (1+ y')} LTZ d = LTZ
  lt-right-incr-neq {y = 0} (LTS ()) d 
  lt-right-incr-neq {x = (1+ x')} {y = (1+ y')} (LTS a) d = LTS (lt-right-incr-neq {x = x'} {y = y'} a λ x → d (foo x))
    where 
      foo : {a b : Nat} -> a == b -> (1+ a) == (1+ b)
      foo eq rewrite eq = refl

  lt-lte-is-lt : {a b c : Nat} -> (a < b) -> (b < (1+ c)) -> (a < c)
  lt-lte-is-lt {a = Z} {c = Z} lt LTZ = lt
  lt-lte-is-lt {a = Z} {c = Z} lt (LTS ())
  lt-lte-is-lt {a = Z} {c = 1+ c} lt lte = LTZ
  lt-lte-is-lt {a = 1+ a} {c = Z} lt LTZ = lt
  lt-lte-is-lt {a = 1+ a} {c = Z} lt (LTS ())
  lt-lte-is-lt {a = 1+ a} {b = 1+ b} {c = 1+ c} (LTS lt) (LTS lte) = LTS (lt-lte-is-lt lt lte)

  trichotomy : (a b : Nat) -> (a < b + b < a + a == b)
  trichotomy Z Z = Inr (Inr refl)
  trichotomy (1+ a) Z = Inr (Inl LTZ)
  trichotomy Z (1+ b) = Inl LTZ
  trichotomy (1+ a) (1+ b) with trichotomy a b  
  ... | Inl x = Inl (LTS x)
  ... | Inr (Inl x) = Inr (Inl (LTS x))
  ... | Inr (Inr x) rewrite x = Inr (Inr refl)

  trichotomy-lemma : {a b : Nat} -> (a == b → ⊥) -> (a < b → ⊥) -> (b < a)
  trichotomy-lemma {a = a} {b = b} neq nlt with trichotomy a b 
  ... | Inl x = abort (nlt x)
  ... | Inr (Inl x) = x
  ... | Inr (Inr x) = abort (neq x)

  _nat+_ : (n m : Nat) → Nat 
  Z nat+ n = n 
  (1+ n) nat+ m = 1+ (n nat+ m)


  -- double : Nat → Nat
  -- double Z = Z 
  -- double (1+ n) = 1+ (1+ (double n))

  -- pair : Nat → Nat → Nat 
  -- pair n Z = double n 
  -- pair n (1+ m) = 1+ (double (pair n m))

  -- data remainder : Set where 
  --   RZ : remainder 
  --   R1 : remainder

  -- half : Nat → (Nat × remainder)
  -- half Z = (Z , RZ) 
  -- half (1+ Z) = (Z , R1) 
  -- half (1+ (1+ n)) with (half n) 
  -- ... | (q , r) = (1+ q , r)

  -- unpair : Nat → (Nat × Nat)
  -- unpair n with half n 
  -- ... | (q , RZ) = (q , Z)
  -- ... | (q , R1) = {!   !}

  -- half-double : (n : Nat) → (half (double n) == (n , RZ))
  -- half-double Z = refl
  -- half-double (1+ n) rewrite (half-double n) = refl

  -- pair-unpair : (n m : Nat) → (unpair (pair n m) == (n , m))
  -- pair-unpair n Z rewrite half-double n = refl
  -- pair-unpair n (1+ m) = {!   !}

  postulate
    pair : (Nat × Nat) → Nat 
    unpair : Nat → (Nat × Nat)
    pair-unpair : (p : Nat × Nat) → (unpair (pair p) == p)
    unpair-pair : (n : Nat) → (pair (unpair n) == n)

  -- data alpha-var-type : Set where 
  --   Bound : (Nat × Nat) → alpha-var-type
  --   Free : Nat → alpha-var-type

  -- postulate
  --   encode-var : alpha-var-type → Nat 
  --   decode-var : Nat → alpha-var-type
  --   encode-decode : (n : alpha-var-type) → (decode-var (encode-var n) == n)
  --   decode-encode : (n : Nat) → (encode-var (decode-var n) == n)

  bijection-injective : {A B : Set} → (f : A → B) → (g : B → A) → ((x : A) → (g (f x) == x)) → ((x : B) → (f (g x) == x)) → (x x' : A) → ((f x) == (f x')) → (x == x')
  bijection-injective f g inv1 inv2 x x' eq with h1 
    where 
      h1 : g (f x) == g (f x')
      h1 rewrite eq = refl
  bijection-injective f g inv1 inv2 x x' eq | h1 rewrite (inv1 x) rewrite (inv1 x') = h1

  pair-inj : ∀{x x' y y'} → ((pair (x' , y')) == (pair (x , y))) → (x' == x) × (y' == y)
  pair-inj {x = x} {x' = x'} {y = y} {y' = y'} eq with bijection-injective pair unpair pair-unpair unpair-pair (x' , y') (x , y) eq 
  ... | refl = refl , refl 
