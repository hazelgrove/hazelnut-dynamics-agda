open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core

module debruijn.debruijn-lemmas-index where
  
  ↑10 : (x : Nat) → (↑Nat 1 0 x) == 1+ x
  ↑10 Z = refl 
  ↑10 (1+ x) rewrite (↑10 x) = refl

  ↑NatZ : (m x : Nat) → ↑Nat Z m x == x
  ↑NatZ Z x = refl
  ↑NatZ (1+ m) Z = refl
  ↑NatZ (1+ m) (1+ x) rewrite ↑NatZ m x = refl

  ↑Z : (m : Nat) → (τ : htyp) → ↑ Z m τ == τ
  ↑Z m b = refl
  ↑Z m (T x) rewrite ↑NatZ m x = refl
  ↑Z m ⦇-⦈ = refl
  ↑Z m (τ ==> τ₁) rewrite ↑Z m τ rewrite ↑Z m τ₁ = refl
  ↑Z m (·∀ τ) rewrite ↑Z (1+ m) τ = refl
  
  ↑Natcompose : (n m x : Nat) → ↑Nat 1 m (↑Nat n m x) == ↑Nat (1+ n) m x
  ↑Natcompose n Z x = refl
  ↑Natcompose Z (1+ m) Z = refl
  ↑Natcompose (1+ n) (1+ m) Z = refl
  ↑Natcompose Z (1+ m) (1+ x) rewrite ↑Natcompose Z m x = refl
  ↑Natcompose (1+ n) (1+ m) (1+ x) rewrite ↑Natcompose (1+ n) m x = refl

  ↑compose : (n m : Nat) → (τ : htyp) → ↑ 1 m (↑ n m τ) == (↑ (1+ n) m τ)
  ↑compose _ _ b = refl
  ↑compose n m (T x) rewrite ↑Natcompose n m x = refl
  ↑compose _ _ ⦇-⦈ = refl
  ↑compose n m (τ ==> τ₁) rewrite ↑compose n m τ rewrite ↑compose n m τ₁ = refl
  ↑compose n m (·∀ τ) rewrite ↑compose n (1+ m) τ = refl

  ↓↑Nat-invert : (m x : Nat) →  ↓Nat 1 m (↑Nat 1 m x) == x
  ↓↑Nat-invert Z x = refl
  ↓↑Nat-invert (1+ m) Z = refl
  ↓↑Nat-invert (1+ m) (1+ x) rewrite ↓↑Nat-invert m x = refl
  
  ↓↑invert : (m : Nat) → (τ : htyp) → ↓ 1 m (↑ 1 m τ) == τ
  ↓↑invert m b = refl 
  ↓↑invert m (T x) rewrite ↓↑Nat-invert m x = refl
  ↓↑invert m ⦇-⦈ = refl
  ↓↑invert m (τ ==> τ₁) rewrite ↓↑invert m τ rewrite ↓↑invert m τ₁ = refl
  ↓↑invert m (·∀ τ) rewrite ↓↑invert (1+ m) τ = refl