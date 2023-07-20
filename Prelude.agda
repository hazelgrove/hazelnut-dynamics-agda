module Prelude where
  open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)

  -- empty type
  data ⊥ : Set where

  -- from false, derive whatever
  abort : ∀ {C : Set} → ⊥ → C
  abort ()

  -- negation 
  open import Agda.Primitive using (Level)
  ¬_ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
  ¬ A = A → ⊥

  -- unit
  data ⊤ : Set where
    <> : ⊤

  -- sums
  data _+_ (A B : Set) : Set where
    Inl : A → A + B
    Inr : B → A + B

  -- pairs
  infixr 1 _,_
  record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (lmax l1 l2) where
    constructor _,_
    field
      π1 : A
      π2 : B π1
  open Σ public

  -- Sigma types, or dependent pairs, with nice notation.
  syntax Σ A (\ x -> B) = Σ[ x ∈ A ] B

  _×_ : {l1 : Level} {l2 : Level} → (Set l1) → (Set l2) → Set (lmax l1 l2)
  A × B = Σ A λ _ → B

  infixr 1 _×_
  infixr 1 _+_

  -- equality
  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
    refl : M == M

  infixr 9 _==_

  -- disequality
  _≠_ : {l : Level} {A : Set l} → (a b : A) → Set l
  a ≠ b = ¬ (a == b)

  {-# BUILTIN EQUALITY _==_ #-}

  -- transitivity of equality
  _·_ : {l : Level} {α : Set l} {x y z : α} → x == y → y == z → x == z
  refl · refl = refl

  -- symmetry of equality
  ! : {l : Level} {α : Set l} {x y : α} → x == y → y == x
  ! refl = refl

  -- ap, in the sense of HoTT, that all functions respect equality in their
  -- arguments. named in a slightly non-standard way to avoid naming
  -- clashes with hazelnut constructors.
  ap1 : {l1 l2 : Level} {α : Set l1} {β : Set l2} {x y : α} (F : α → β)
          → x == y → F x == F y
  ap1 F refl = refl

  -- transport, in the sense of HoTT, that fibrations respect equality
  tr : {l1 l2 : Level} {α : Set l1} {x y : α}
                    (B : α → Set l2)
                    → x == y
                    → B x
                    → B y
  tr B refl x₁ = x₁

  -- options
  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  -- the some constructor is injective. perhaps unsurprisingly.
  someinj : {A : Set} {x y : A} → Some x == Some y → x == y
  someinj refl = refl

  --  some isn't none.
  somenotnone : {A : Set} {x : A} → Some x == None → ⊥
  somenotnone ()

  -- function extensionality, used to reason about contexts as finite
  -- functions.
  postulate
     funext : {A : Set} {B : A → Set} {f g : (x : A) → (B x)} → ((x : A) → f x == g x) → f == g

  -- non-equality is commutative
  flip : {A : Set} {x y : A} → (x == y → ⊥) → (y == x → ⊥)
  flip neq eq = neq (! eq)

    -- equality is symmetric
  sym : {A : Set} {x y : A} → (x == y) → (y == x)
  sym refl = refl
