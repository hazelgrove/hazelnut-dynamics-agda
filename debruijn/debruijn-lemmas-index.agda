open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core

module debruijn.debruijn-lemmas-index where
  
  ↑10 : (x : Nat) → (↑Nat Z 1 x) == 1+ x
  ↑10 Z = refl 
  ↑10 (1+ x) rewrite (↑10 x) = refl

  ↑NatZ : (t x : Nat) → ↑Nat t Z x == x
  ↑NatZ Z x = refl
  ↑NatZ (1+ t) Z = refl
  ↑NatZ (1+ t) (1+ x) rewrite ↑NatZ t x = refl

  ↑Z : (t : Nat) → (τ : htyp) → ↑ t Z τ == τ
  ↑Z t b = refl
  ↑Z t (T x) rewrite ↑NatZ t x = refl
  ↑Z t ⦇-⦈ = refl
  ↑Z t (τ ==> τ₁) rewrite ↑Z t τ rewrite ↑Z t τ₁ = refl
  ↑Z t (·∀ τ) rewrite ↑Z (1+ t) τ = refl
  
  ↑Natcompose : (t i x : Nat) → ↑Nat t 1 (↑Nat t i x) == ↑Nat t (1+ i) x
  ↑Natcompose Z Z x = refl
  ↑Natcompose Z (1+ i) x = refl
  ↑Natcompose (1+ t) i Z = refl
  ↑Natcompose (1+ t) i (1+ x) rewrite ↑Natcompose t i x = refl

  ↑compose : (t i : Nat) → (τ : htyp) → ↑ t 1 (↑ t i τ) == (↑ t (1+ i) τ)
  ↑compose _ _ b = refl
  ↑compose t i (T x) rewrite ↑Natcompose t i x = refl
  ↑compose _ _ ⦇-⦈ = refl
  ↑compose t i (τ ==> τ₁) rewrite ↑compose t i τ rewrite ↑compose t i τ₁ = refl
  ↑compose t i (·∀ τ) rewrite ↑compose (1+ t) i τ = refl

  ↑d-compose : (t i : Nat) → (d : ihexp) → ↑d t 1 (↑d t i d) == (↑d t (1+ i) d)
  ↑d-compose t i c = refl
  ↑d-compose t i (X x) rewrite ↑Natcompose t i x = refl
  ↑d-compose t i (·λ[ x ] d) rewrite ↑d-compose (1+ t) i d = refl
  ↑d-compose t i (·Λ d) rewrite ↑d-compose t i d = refl
  ↑d-compose t i ⦇-⦈⟨ x ⟩ = refl
  ↑d-compose t i ⦇⌜ d ⌟⦈⟨ x ⟩ rewrite ↑d-compose t i d = refl
  ↑d-compose t i (d ∘ d₁) rewrite ↑d-compose t i d rewrite ↑d-compose t i d₁ = refl
  ↑d-compose t i (d < x >) rewrite ↑d-compose t i d = refl
  ↑d-compose t i (d ⟨ x ⇒ x₁ ⟩) rewrite ↑d-compose t i d = refl
  ↑d-compose t i (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑d-compose t i d = refl


  ↓↑Nat-invert : (t x : Nat) → ↓Nat t 1 (↑Nat t 1 x) == x
  ↓↑Nat-invert Z x = refl 
  ↓↑Nat-invert (1+ t) Z = refl
  ↓↑Nat-invert (1+ t) (1+ x) rewrite ↓↑Nat-invert t x = refl
  
  ↓↑invert : (t : Nat) → (τ : htyp) → ↓ t 1 (↑ t 1 τ) == τ
  ↓↑invert t b = refl 
  ↓↑invert t (T x) rewrite ↓↑Nat-invert t x = refl
  ↓↑invert t ⦇-⦈ = refl
  ↓↑invert t (τ ==> τ₁) rewrite ↓↑invert t τ rewrite ↓↑invert t τ₁ = refl
  ↓↑invert t (·∀ τ) rewrite ↓↑invert (1+ t) τ = refl