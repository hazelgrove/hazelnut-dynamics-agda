
open import Prelude
open import Nat
open import core-type
open import core-exp

module core-subst where

  -- [↑Nat threshold increase index] equals
  -- [increase] + [index] if [index] >= [threshold]
  -- else [index]
  ↑Nat : (t i n : Nat) → Nat
  ↑Nat Z Z n = n
  ↑Nat Z (1+ i) n = 1+ (↑Nat Z i n)
  ↑Nat (1+ t) i Z = Z
  ↑Nat (1+ t) i (1+ n) = 1+ (↑Nat t i n)

  ↓Nat : (t d n : Nat) → Nat
  ↓Nat Z Z x = x
  ↓Nat Z (1+ d) Z = Z -- this case shouldn't happen
  ↓Nat Z (1+ d) (1+ n) = ↓Nat Z d n
  ↓Nat (1+ t) d Z = Z
  ↓Nat (1+ t) d (1+ n) = 1+ (↓Nat t d n)

  -- [↑ threshold increase tau] equals
  -- [tau] with all variables that are free
  -- by a margin of at least [threshold]
  -- increased by [increase]
  ↑ : (t i : Nat) → htyp → htyp 
  ↑ t i (T x) = T (↑Nat t i x )
  ↑ t i b = b
  ↑ t i ⦇-⦈ = ⦇-⦈
  ↑ t i (τ1 ==> τ2) = (↑ t i τ1) ==> (↑ t i τ2)
  ↑ t i (·∀ τ) = ·∀ (↑ (1+ t) i τ)

  ↓ : Nat → Nat → htyp → htyp 
  ↓ t d (T x) = T (↓Nat t d x)
  ↓ t d b = b
  ↓ t d ⦇-⦈ = ⦇-⦈
  ↓ t d (τ1 ==> τ2) = (↓ t d τ1) ==> (↓ t d τ2)
  ↓ t d (·∀ τ) = ·∀ (↓ (1+ t) d τ)
  
  ↑ctx : (t i : Nat) → ctx → ctx 
  ↑ctx t i ∅ = ∅
  ↑ctx t i (τ , ctx) = (↑ t i τ , ↑ctx t i ctx)
  ↑ctx t i (TVar, ctx) = (TVar, ↑ctx (1+ t) i ctx)

  ↑d : (t1 n t2 m : Nat) → ihexp → ihexp 
  ↑d t1 n t2 m c = c
  ↑d t1 n t2 m (X x) = X (↑Nat t1 n x)
  ↑d t1 n t2 m (·λ[ τ ] d) = ·λ[ ↑ t2 m τ ] (↑d (1+ t1) n t2 m d)
  ↑d t1 n t2 m (·Λ d) = ·Λ (↑d t1 n (1+ t2) m d)
  ↑d t1 n t2 m ⦇-⦈ = ⦇-⦈
  ↑d t1 n t2 m ⦇⌜ d ⌟⦈ = ⦇⌜ ↑d t1 n t2 m d ⌟⦈
  ↑d t1 n t2 m (d1 ∘ d2) = (↑d t1 n t2 m d1) ∘ (↑d t1 n t2 m d2)
  ↑d t1 n t2 m (d < τ >) = (↑d t1 n t2 m d) < ↑ t2 m τ >
  ↑d t1 n t2 m (d ⟨ τ1 ⇒ τ2 ⟩) = (↑d t1 n t2 m d) ⟨ (↑ t2 m τ1) ⇒ (↑ t2 m τ2) ⟩
  ↑d t1 n t2 m (d ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩) = (↑d t1 n t2 m d) ⟨ (↑ t2 m τ1) ⇒⦇-⦈⇏ (↑ t2 m τ3) ⟩

  TTSub : Nat → htyp → htyp → htyp
  TTSub n τ b = b
  TTSub n τ ⦇-⦈ = ⦇-⦈  
  TTSub n τ (τ1 ==> τ2) = (TTSub n τ τ1) ==> (TTSub n τ τ2)
  TTSub n τ1 (·∀ τ2) = ·∀ (TTSub (1+ n) τ1 τ2)
  TTSub n τ (T m) with natEQ n m 
  ... | Inl refl = ↓ n 1 (↑ Z (1+ n) τ)
  ... | Inr neq = T (↓Nat n 1 m)
  
  TtSub : Nat → htyp → ihexp → ihexp
  TtSub n τ c = c
  TtSub n τ (X x) = X x
  TtSub n τ (·λ[ x ] d) = ·λ[ TTSub n τ x ] (TtSub n τ d)
  TtSub n τ (·Λ d) = ·Λ (TtSub (1+ n) τ d)
  TtSub n τ ⦇-⦈ = ⦇-⦈
  TtSub n τ ⦇⌜ d ⌟⦈ = ⦇⌜ TtSub n τ d ⌟⦈
  TtSub n τ (d ∘ d₁) = (TtSub n τ d) ∘ (TtSub n τ d₁)
  TtSub n τ (d < x >) = (TtSub n τ d) < TTSub n τ x >
  TtSub n τ (d ⟨ x ⇒ x₁ ⟩) = (TtSub n τ d) ⟨ TTSub n τ x ⇒ TTSub n τ x₁ ⟩
  TtSub n τ (d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) = (TtSub n τ d) ⟨ TTSub n τ x ⇒⦇-⦈⇏ TTSub n τ x₁ ⟩

  ttSub : Nat → Nat → ihexp → ihexp → ihexp 
  ttSub n m d1 c = c
  ttSub n m d1 ⦇-⦈ = ⦇-⦈
  ttSub n m d1 ⦇⌜ d2 ⌟⦈ = ⦇⌜ ttSub n m d1 d2 ⌟⦈
  ttSub n m d1 (d2 ∘ d3) = (ttSub n m d1 d2) ∘ (ttSub n m d1 d3)
  ttSub n m d1 (d2 < x >) = (ttSub n m d1 d2) < x >
  ttSub n m d1 (d2 ⟨ x ⇒ x₁ ⟩) = (ttSub n m d1 d2) ⟨ x ⇒ x₁ ⟩
  ttSub n m d1 (d2 ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) = (ttSub n m d1 d2) ⟨ x ⇒⦇-⦈⇏ x₁ ⟩
  ttSub n m d1 (·λ[ x ] d2) = ·λ[ x ] (ttSub (1+ n) m d1 d2)
  ttSub n m d1 (·Λ d2) = ·Λ (ttSub n (1+ m) d1 d2)
  ttSub n m d (X x) with natEQ x n 
  ... | Inl refl = ↑d 0 n 0 m d
  ... | Inr neq = X (↓Nat n 1 x)
 
  -- assumes tau is closed, otherwise need to increment fv's in tau in last case
  TCtxSub : Nat → htyp → ctx → ctx 
  TCtxSub n τ ∅ = ∅
  TCtxSub n τ (x , Γ) = (TTSub n τ x) , (TCtxSub n τ Γ)
  TCtxSub Z τ (TVar, Γ) = Γ
  TCtxSub (1+ n) τ (TVar, Γ) = TVar, TCtxSub n τ Γ