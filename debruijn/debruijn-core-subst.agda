
open import Prelude
open import Nat
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp

module debruijn.debruijn-core-subst where

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
 
  TCtxSub : Nat → htyp → ctx → ctx 
  TCtxSub n τ ∅ = ∅
  TCtxSub n τ (x , Γ) = (TTSub n τ x) , (TCtxSub n τ Γ)
  TCtxSub Z τ (TVar, Γ) = (TVar, Γ)
  TCtxSub (1+ n) τ (TVar, Γ) = TVar, TCtxSub n τ Γ

  -------------------------------------------------------------
  --- Not in use, retained for proof of correctness:
  -------------------------------------------------------------

  ↑d' : (t i : Nat) → ihexp → ihexp 
  ↑d' t i c = c
  ↑d' t i (X x) = X (↑Nat t i x)
  ↑d' t i (·λ[ τ ] d) = ·λ[ τ ] (↑d' (1+ t) i d)
  ↑d' t i (·Λ d) = ·Λ (↑d' t i d)
  ↑d' t i ⦇-⦈ = ⦇-⦈
  ↑d' t i ⦇⌜ d ⌟⦈ = ⦇⌜ ↑d' t i d ⌟⦈
  ↑d' t i (d1 ∘ d2) = (↑d' t i d1) ∘ (↑d' t i d2)
  ↑d' t i (d < τ >) = (↑d' t i d) < τ >
  ↑d' t i (d ⟨ τ1 ⇒ τ2 ⟩) = (↑d' t i d) ⟨ τ1 ⇒ τ2 ⟩
  ↑d' t i (d ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩) = (↑d' t i d) ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩

  ↓d' : (t i : Nat) → ihexp → ihexp 
  ↓d' t i c = c
  ↓d' t i (X x) = X (↓Nat t i x)
  ↓d' t i (·λ[ τ ] d) = ·λ[ τ ] (↓d' (1+ t) i d)
  ↓d' t i (·Λ d) = ·Λ (↓d' t i d)
  ↓d' t i ⦇-⦈ = ⦇-⦈
  ↓d' t i ⦇⌜ d ⌟⦈ = ⦇⌜ ↓d' t i d ⌟⦈
  ↓d' t i (d1 ∘ d2) = (↓d' t i d1) ∘ (↓d' t i d2)
  ↓d' t i (d < τ >) = (↓d' t i d) < τ >
  ↓d' t i (d ⟨ τ1 ⇒ τ2 ⟩) = (↓d' t i d) ⟨ τ1 ⇒ τ2 ⟩
  ↓d' t i (d ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩) = (↓d' t i d) ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩

  ↑td : (t i : Nat) → ihexp → ihexp 
  ↑td t i c = c
  ↑td t i (X x) = X x
  ↑td t i (·λ[ τ ] d) = ·λ[ ↑ t i τ ] (↑td t i d)
  ↑td t i (·Λ d) = ·Λ (↑td (1+ t) i d)
  ↑td t i ⦇-⦈ = ⦇-⦈
  ↑td t i ⦇⌜ d ⌟⦈ = ⦇⌜ (↑td t i d) ⌟⦈
  ↑td t i (d1 ∘ d2) = (↑td t i d1) ∘ (↑td t i d2)
  ↑td t i (d < τ >) = (↑td t i d) < ↑ t i τ >  
  ↑td t i (d ⟨ τ1 ⇒ τ2 ⟩) = (↑td t i d) ⟨ ↑ t i τ1 ⇒ ↑ t i τ2 ⟩
  ↑td t i (d ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩) = (↑td t i d) ⟨ ↑ t i τ1 ⇒⦇-⦈⇏ ↑ t i τ3 ⟩

  ↓td : (t i : Nat) → ihexp → ihexp 
  ↓td t i c = c
  ↓td t i (X x) = X x
  ↓td t i (·λ[ τ ] d) = ·λ[ ↓ t i τ ] (↓td t i d)
  ↓td t i (·Λ d) = ·Λ (↓td (1+ t) i d)
  ↓td t i ⦇-⦈ = ⦇-⦈
  ↓td t i ⦇⌜ d ⌟⦈ = ⦇⌜ (↓td t i d) ⌟⦈
  ↓td t i (d1 ∘ d2) = (↓td t i d1) ∘ (↓td t i d2)
  ↓td t i (d < τ >) = (↓td t i d) < ↓ t i τ >  
  ↓td t i (d ⟨ τ1 ⇒ τ2 ⟩) = (↓td t i d) ⟨ ↓ t i τ1 ⇒ ↓ t i τ2 ⟩
  ↓td t i (d ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩) = (↓td t i d) ⟨ ↓ t i τ1 ⇒⦇-⦈⇏ ↓ t i τ3 ⟩

  -- substitution of types in types
  TT[_/_]_ : htyp → Nat → htyp → htyp 
  TT[ τ / n ] b = b
  TT[ τ / n ] T m with natEQ n m 
  ... | Inl refl = τ
  ... | Inr neq = T m
  TT[ τ / n ] ⦇-⦈ = ⦇-⦈
  TT[ τ / n ] (τ1 ==> τ2) = ((TT[ τ / n ] τ1) ==> (TT[ τ / n ] τ2))
  TT[ τ / n ] (·∀ τ') = ·∀ (TT[ (↑ Z 1 τ) / 1+ n ] τ')

  -- substitutes for the free variable that is n-steps free
  TTSub' : Nat → htyp → htyp → htyp 
  TTSub' n τ1 τ2 = ↓ n 1 (TT[ (↑ Z (1+ n) τ1) / n ] τ2)

  -- substitution of types in terms 
  Tt[_/_]_ : htyp → Nat → ihexp → ihexp
  Tt[ τ / t ] c = c
  Tt[ τ / t ] (X x) = X x
  Tt[ τ / t ] (·λ[ τx ] d) = ·λ[ TT[ τ / t ] τx ] (Tt[ τ / t ] d)
  Tt[ τ / t ] (·Λ d) = ·Λ (Tt[ (↑ Z 1 τ) / 1+ t ] d) 
  Tt[ τ / t ] (⦇-⦈) = ⦇-⦈
  Tt[ τ / t ] (⦇⌜ d ⌟⦈) = ⦇⌜ (Tt[ τ / t ] d) ⌟⦈
  Tt[ τ / t ] (d1 ∘ d2) = (Tt[ τ / t ] d1) ∘ (Tt[ τ / t ] d2)
  Tt[ τ / t ] (d < τ' >) = (Tt[ τ / t ] d) < TT[ τ / t ] τ' >
  Tt[ τ / t ] (d ⟨ τ1 ⇒ τ2 ⟩ ) = (Tt[ τ / t ] d) ⟨ (TT[ τ / t ] τ1) ⇒ (TT[ τ / t ] τ2) ⟩
  Tt[ τ / t ] (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = (Tt[ τ / t ] d) ⟨ (TT[ τ / t ] τ1) ⇒⦇-⦈⇏ (TT[ τ / t ] τ2) ⟩

  TtSub' : Nat → htyp → ihexp → ihexp
  TtSub' n τ d = ↓td n 1 (Tt[ (↑ Z (1+ n) τ) / n ] d)

  -- substitution of terms in terms
  [_/_]_ : ihexp → Nat → ihexp → ihexp
  [ d / n ] c = c
  [ d / n ] X m with natEQ m n
  ... | Inl refl = d
  ... | Inr neq = X m
  [ d / n ] (·λ[ τ ] d') = ·λ[ τ ] ([ (↑d' Z 1 d) / 1+ n ] d')
  [ d / n ] ·Λ d' = ·Λ ([ ↑td Z 1 d / n ] d')
  [ d / n ] ⦇-⦈ = ⦇-⦈
  [ d / n ] ⦇⌜ d' ⌟⦈ =  ⦇⌜ [ d / n ] d' ⌟⦈
  [ d / n ] (d1 ∘ d2) = ([ d / n ] d1) ∘ ([ d / n ] d2)
  [ d / n ] (d' < τ >) = ([ d / n ] d') < τ >
  [ d / n ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / n ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / n ] (d' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = ([ d / n ] d') ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩

  ttSub' : Nat → Nat → ihexp → ihexp → ihexp 
  ttSub' n m d1 d2 = ↓d' n 1 ([ ↑td Z m (↑d' Z (1+ n) d1) / n ] d2)
