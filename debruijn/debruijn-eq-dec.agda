
open import Prelude
open import Nat
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp

module debruijn.debruijn-eq-dec where

  htyp-eq-dec : (τ1 τ2 : htyp) → (τ1 == τ2) + (τ1 ≠ τ2)
  htyp-eq-dec b b = Inl refl
  htyp-eq-dec b (T x) = Inr (λ ())
  htyp-eq-dec b ⦇-⦈ = Inr (λ ())
  htyp-eq-dec b (τ2 ==> τ3) = Inr (λ ())
  htyp-eq-dec b (·∀ τ2) = Inr (λ ())
  htyp-eq-dec (T x) b = Inr (λ ())
  htyp-eq-dec (T x) (T y) with natEQ x y 
  ... | Inl refl = Inl refl  
  ... | Inr neq = Inr λ x₁ → neq (h1 x₁)
    where 
      h1 : T x == T y → x == y
      h1 refl = refl 
  htyp-eq-dec (T x) ⦇-⦈ = Inr (λ ())
  htyp-eq-dec (T x) (τ2 ==> τ3) = Inr (λ ())
  htyp-eq-dec (T x) (·∀ τ2) = Inr (λ ())
  htyp-eq-dec ⦇-⦈ b = Inr (λ ())
  htyp-eq-dec ⦇-⦈ (T x) = Inr (λ ())
  htyp-eq-dec ⦇-⦈ ⦇-⦈ = Inl refl
  htyp-eq-dec ⦇-⦈ (τ2 ==> τ3) = Inr (λ ())
  htyp-eq-dec ⦇-⦈ (·∀ τ2) = Inr (λ ())
  htyp-eq-dec (τ1 ==> τ2) b = Inr (λ ())
  htyp-eq-dec (τ1 ==> τ2) (T x) = Inr (λ ())
  htyp-eq-dec (τ1 ==> τ2) ⦇-⦈ = Inr (λ ())
  htyp-eq-dec (τ1 ==> τ2) (τ3 ==> τ4) with htyp-eq-dec τ1 τ3 | htyp-eq-dec τ2 τ4 
  ... | Inl refl | Inl refl = Inl refl
  ... | _ | Inr x = Inr λ x₁ → x (h1 x₁)
    where 
      h1 : (τ1 ==> τ2) == (τ3 ==> τ4) → τ2 == τ4
      h1 refl = refl
  ... | Inr x | _ = Inr λ x₁ → x (h1 x₁)
    where 
      h1 : (τ1 ==> τ2) == (τ3 ==> τ4) → τ1 == τ3
      h1 refl = refl
  htyp-eq-dec (τ1 ==> τ2) (·∀ τ3) = Inr (λ ())
  htyp-eq-dec (·∀ τ1) b = Inr (λ ())
  htyp-eq-dec (·∀ τ1) (T x) = Inr (λ ())
  htyp-eq-dec (·∀ τ1) ⦇-⦈ = Inr (λ ())
  htyp-eq-dec (·∀ τ1) (τ2 ==> τ3) = Inr (λ ())
  htyp-eq-dec (·∀ τ1) (·∀ τ2) with htyp-eq-dec τ1 τ2 
  ... | Inl refl = Inl refl
  ... | Inr neq = Inr λ x → neq (h1 x)
    where 
      h1 : ·∀ τ1 == ·∀ τ2 → τ1 == τ2
      h1 refl = refl