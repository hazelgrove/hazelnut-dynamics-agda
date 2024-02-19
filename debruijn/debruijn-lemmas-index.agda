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

  ↑td-compose : (t i : Nat) → (d : ihexp) → ↑td t 1 (↑td t i d) == (↑td t (1+ i) d)
  ↑td-compose t i c = refl
  ↑td-compose t i (X x) rewrite ↑Natcompose t i x = refl
  ↑td-compose t i (·λ[ x ] d) rewrite ↑td-compose t i d rewrite ↑compose t i x = refl
  ↑td-compose t i (·Λ d) rewrite ↑td-compose (1+ t) i d = refl
  ↑td-compose t i ⦇-⦈⟨ x ⟩ rewrite ↑compose t i x = refl
  ↑td-compose t i ⦇⌜ d ⌟⦈⟨ x ⟩ rewrite ↑td-compose t i d rewrite ↑compose t i x = refl
  ↑td-compose t i (d ∘ d₁) rewrite ↑td-compose t i d rewrite ↑td-compose t i d₁ = refl
  ↑td-compose t i (d < x >) rewrite ↑td-compose t i d rewrite ↑compose t i x = refl
  ↑td-compose t i (d ⟨ x ⇒ x₁ ⟩) rewrite ↑td-compose t i d rewrite ↑compose t i x rewrite ↑compose t i x₁ = refl
  ↑td-compose t i (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) rewrite ↑td-compose t i d rewrite ↑compose t i x rewrite ↑compose t i x₁ = refl

  ↑ctx-compose : (t i : Nat) → (Γ : ctx) → ↑ctx t 1 (↑ctx t i Γ) == (↑ctx t (1+ i) Γ)
  ↑ctx-compose t i ∅ = refl
  ↑ctx-compose t i (x , Γ) rewrite ↑compose t i x rewrite ↑ctx-compose t i Γ = refl

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
  ↓↑d-invert {d = c} = refl 
  ↓↑d-invert {n = n} {m = m} {d = X x} rewrite ↓↑Nat-invert-strong n m x = refl  
  ↓↑d-invert {n = n} {m = m} {d = ·λ[ x ] d} rewrite nat+comm 1 n with ↓↑d-invert {n = n} {m = 1+ m} {d = d} 
  ... | result rewrite nat+1+ n m rewrite result = refl
  ↓↑d-invert {n = n} {m = m} {d = ·Λ d} rewrite ↓↑d-invert {n = n} {m = m} {d = d} = refl
  ↓↑d-invert {d = ⦇-⦈⟨ x ⟩} = refl
  ↓↑d-invert {n = n} {m = m} {d = ⦇⌜ d ⌟⦈⟨ x ⟩} rewrite ↓↑d-invert {n = n} {m = m} {d = d} = refl
  ↓↑d-invert {n = n} {m = m} {d = d1 ∘ d2} rewrite ↓↑d-invert {n = n} {m = m} {d = d1} rewrite ↓↑d-invert {n = n} {m = m} {d = d2} = refl
  ↓↑d-invert {n = n} {m = m} {d = d < x >} rewrite ↓↑d-invert {n = n} {m = m} {d = d} = refl
  ↓↑d-invert {n = n} {m = m} {d = d ⟨ x ⇒ x₁ ⟩} rewrite ↓↑d-invert {n = n} {m = m} {d = d} = refl    
  ↓↑d-invert {n = n} {m = m} {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} rewrite ↓↑d-invert {n = n} {m = m} {d = d} = refl 

  ↑d-↑td-comm : ∀{n m t s d} → ↑d t n (↑td s m d) == ↑td s m (↑d t n d)
  ↑d-↑td-comm {d = c} = refl 
  ↑d-↑td-comm {d = X x} = refl
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ·λ[ x ] d} rewrite ↑d-↑td-comm {n = n} {m = m} {t = 1+ t} {s = s} {d = d} = refl 
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ·Λ d} rewrite ↑d-↑td-comm {n = n} {m = m} {t = t} {s = 1+ s} {d = d} = refl
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ⦇-⦈⟨ x ⟩} = refl
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = ⦇⌜ d ⌟⦈⟨ x ⟩} rewrite ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d ∘ d₁} 
    rewrite ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d}
    rewrite ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d₁} = refl
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d < x >} rewrite ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d ⟨ x ⇒ x₁ ⟩} rewrite ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl
  ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} rewrite ↑d-↑td-comm {n = n} {m = m} {t = t} {s = s} {d = d} = refl