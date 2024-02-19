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

  ↑dZ : (t : Nat) → (d : ihexp) → ↑d t Z d == d
  ↑dZ t c = refl
  ↑dZ t (X x) rewrite ↑NatZ t x = refl
  ↑dZ t (·λ[ x ] d) rewrite ↑dZ (1+ t) d = refl
  ↑dZ t (·Λ d) rewrite ↑dZ t d = refl
  ↑dZ t ⦇-⦈⟨ x ⟩ = refl
  ↑dZ t ⦇⌜ d ⌟⦈⟨ x ⟩ rewrite ↑dZ t d = refl
  ↑dZ t (d1 ∘ d2) rewrite ↑dZ t d1 rewrite ↑dZ t d2 = refl
  ↑dZ t (d < x >) rewrite ↑dZ t d = refl
  ↑dZ t (d ⟨ x ⇒ x₁ ⟩) rewrite ↑dZ t d = refl
  ↑dZ t (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑dZ t d = refl

  ↑tdZ : (t : Nat) → (d : ihexp) → ↑td t Z d == d
  ↑tdZ t c = refl
  ↑tdZ t (X x) = refl
  ↑tdZ t (·λ[ x ] d) rewrite ↑Z t x rewrite ↑tdZ t d = refl
  ↑tdZ t (·Λ d) rewrite ↑tdZ (1+ t) d = refl
  ↑tdZ t ⦇-⦈⟨ x ⟩ rewrite ↑Z t x = refl
  ↑tdZ t ⦇⌜ d ⌟⦈⟨ x ⟩ rewrite ↑Z t x rewrite ↑tdZ t d = refl
  ↑tdZ t (d1 ∘ d2) rewrite ↑tdZ t d1 rewrite ↑tdZ t d2 = refl
  ↑tdZ t (d < x >) rewrite ↑Z t x rewrite ↑tdZ t d = refl
  ↑tdZ t (d ⟨ x1 ⇒ x2 ⟩) rewrite ↑Z t x1 rewrite ↑Z t x2 rewrite ↑tdZ t d = refl
  ↑tdZ t (d ⟨ x1 ⇒⦇-⦈⇏ x2 ⟩) rewrite ↑Z t x1 rewrite ↑Z t x2 rewrite ↑tdZ t d = refl

  
  ↑Natcompose : (t i x : Nat) → ↑Nat t 1 (↑Nat t i x) == ↑Nat t (1+ i) x
  ↑Natcompose Z Z x = refl
  ↑Natcompose Z (1+ i) x = refl
  ↑Natcompose (1+ t) i Z = refl
  ↑Natcompose (1+ t) i (1+ x) rewrite ↑Natcompose t i x = refl

  ↑compose : (t i : Nat) → (τ : htyp) → ↑ t 1 (↑ t i τ) == (↑ t (1+ i) τ)
  ↑compose _ Z t = refl
  ↑compose _ (1+ _) b = refl
  ↑compose t (1+ i) (T x) rewrite ↑Natcompose t (1+ i) x = refl
  ↑compose _ (1+ _) ⦇-⦈ = refl
  ↑compose t (1+ i) (τ ==> τ₁) rewrite ↑compose t (1+ i) τ rewrite ↑compose t (1+ i) τ₁ = refl
  ↑compose t (1+ i) (·∀ τ) rewrite ↑compose (1+ t) (1+ i) τ = refl

  ↑d-compose : (t i : Nat) → (d : ihexp) → ↑d t 1 (↑d t i d) == (↑d t (1+ i) d)
  ↑d-compose t Z d = refl
  ↑d-compose t (1+ i) c = refl
  ↑d-compose t (1+ i) (X x) rewrite ↑Natcompose t (1+ i) x = refl
  ↑d-compose t (1+ i) (·λ[ x ] d) rewrite ↑d-compose (1+ t) (1+ i) d = refl
  ↑d-compose t (1+ i) (·Λ d) rewrite ↑d-compose t (1+ i) d = refl
  ↑d-compose t (1+ i) ⦇-⦈⟨ x ⟩ = refl
  ↑d-compose t (1+ i) ⦇⌜ d ⌟⦈⟨ x ⟩ rewrite ↑d-compose t (1+ i) d = refl
  ↑d-compose t (1+ i) (d ∘ d₁) rewrite ↑d-compose t (1+ i) d rewrite ↑d-compose t (1+ i) d₁ = refl
  ↑d-compose t (1+ i) (d < x >) rewrite ↑d-compose t (1+ i) d = refl
  ↑d-compose t (1+ i) (d ⟨ x ⇒ x₁ ⟩) rewrite ↑d-compose t (1+ i) d = refl
  ↑d-compose t (1+ i) (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑d-compose t (1+ i) d = refl

  ↑ctx-compose : (t i : Nat) → (Γ : ctx) → ↑ctx t 1 (↑ctx t i Γ) == (↑ctx t (1+ i) Γ)
  ↑ctx-compose t Z Γ = refl
  ↑ctx-compose t (1+ i) ∅ = refl
  ↑ctx-compose t (1+ i) (x , Γ) rewrite ↑compose t (1+ i) x rewrite ↑ctx-compose t (1+ i) Γ = refl

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

  -- ↓↑d-invert : ∀{n d} → ↓d n 1 (↑d a (b nat+ c nat+ d) d) == ↑d 0 n d

  ↓↑Nat-invert-strong : (n m x : Nat) → ↓Nat (n nat+ m) 1 (↑Nat m (n nat+ 1) x) == ↑Nat m n x
  ↓↑Nat-invert-strong Z m x rewrite ↑NatZ m x = ↓↑Nat-invert m x
  ↓↑Nat-invert-strong (1+ n) Z x rewrite nat+Z n with ↓↑Nat-invert-strong n Z x
  ... | result rewrite nat+Z n rewrite result = refl
  ↓↑Nat-invert-strong (1+ n) (1+ m) Z = refl
  ↓↑Nat-invert-strong (1+ n) (1+ m) (1+ x) with ↓↑Nat-invert-strong (1+ n) m x 
  ... | result rewrite nat+1+ n m rewrite result = refl
    
  ↓↑d-invert : ∀{n m d} → ↓d (n nat+ m) 1 (↑d m (n nat+ 1) d) == ↑d m n d
  ↓↑d-invert {n = Z} {d = c} = refl
  ↓↑d-invert {n = Z} {m = m} {d = X x} rewrite ↓↑Nat-invert m x = refl 
  ↓↑d-invert {n = Z} {m = m} {d = ·λ[ x ] d} rewrite ↓↑d-invert {n = Z} {m = 1+ m} {d = d} = refl
  ↓↑d-invert {n = Z} {m = m} {d = ·Λ d} rewrite ↓↑d-invert {n = Z} {m = m} {d = d} = refl
  ↓↑d-invert {n = Z} {m = m} {d = ⦇-⦈⟨ x ⟩} = refl
  ↓↑d-invert {n = Z} {m = m} {d = ⦇⌜ d ⌟⦈⟨ x ⟩} rewrite ↓↑d-invert {n = Z} {m = m} {d = d} = refl
  ↓↑d-invert {n = Z} {m = m} {d = d ∘ d₁} rewrite ↓↑d-invert {n = Z} {m = m} {d = d} rewrite ↓↑d-invert {n = Z} {m = m} {d = d₁} = refl
  ↓↑d-invert {n = Z} {m = m} {d = d < x >} rewrite ↓↑d-invert {n = Z} {m = m} {d = d} = refl
  ↓↑d-invert {n = Z} {m = m} {d = d ⟨ x ⇒ x₁ ⟩} rewrite ↓↑d-invert {n = Z} {m = m} {d = d} = refl
  ↓↑d-invert {n = Z} {m = m} {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩}rewrite ↓↑d-invert {n = Z} {m = m} {d = d}  = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = c} = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = X x} rewrite ↓↑Nat-invert-strong (1+ n) m x = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = ·λ[ x ] d} with ↓↑d-invert {n = 1+ n} {m = 1+ m} {d = d} 
  ... | result rewrite nat+1+ n m rewrite result = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = ·Λ d} rewrite ↓↑d-invert {n = 1+ n} {m = m} {d = d} = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = ⦇-⦈⟨ x ⟩} = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = ⦇⌜ d ⌟⦈⟨ x ⟩} rewrite ↓↑d-invert {n = 1+ n} {m = m} {d = d} = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = d ∘ d₁} rewrite ↓↑d-invert {n = 1+ n} {m = m} {d = d} rewrite ↓↑d-invert {n = 1+ n} {m = m} {d = d₁} = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = d < x >} rewrite ↓↑d-invert {n = 1+ n} {m = m} {d = d} = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = d ⟨ x ⇒ x₁ ⟩} rewrite ↓↑d-invert {n = 1+ n} {m = m} {d = d} = refl
  ↓↑d-invert {n = 1+ n} {m = m} {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩}rewrite ↓↑d-invert {n = 1+ n} {m = m} {d = d}  = refl