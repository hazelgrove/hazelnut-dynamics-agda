
open import Prelude
open import Nat
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp

module debruijn.debruijn-core where

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

  ↑d : (t i : Nat) → ihexp → ihexp 
  ↑d t i c = c
  ↑d t i (X x) = X (↑Nat t i x)
  ↑d t i (·λ[ τ ] d) = ·λ[ τ ] (↑d (1+ t) i d)
  ↑d t i (·Λ d) = ·Λ (↑d t i d)
  ↑d t i ⦇-⦈⟨ τ ⟩ = ⦇-⦈⟨ τ ⟩
  ↑d t i ⦇⌜ d ⌟⦈⟨ τ ⟩ = ⦇⌜ ↑d t i d ⌟⦈⟨ τ ⟩
  ↑d t i (d1 ∘ d2) = (↑d t i d1) ∘ (↑d t i d2)
  ↑d t i (d < τ >) = (↑d t i d) < τ >
  ↑d t i (d ⟨ τ1 ⇒ τ2 ⟩) = (↑d t i d) ⟨ τ1 ⇒ τ2 ⟩
  ↑d t i (d ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩) = (↑d t i d) ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩

  ↓d : (t i : Nat) → ihexp → ihexp 
  ↓d t i c = c
  ↓d t i (X x) = X (↓Nat t i x)
  ↓d t i (·λ[ τ ] d) = ·λ[ τ ] (↓d (1+ t) i d)
  ↓d t i (·Λ d) = ·Λ (↓d t i d)
  ↓d t i ⦇-⦈⟨ τ ⟩ = ⦇-⦈⟨ τ ⟩
  ↓d t i ⦇⌜ d ⌟⦈⟨ τ ⟩ = ⦇⌜ ↓d t i d ⌟⦈⟨ τ ⟩
  ↓d t i (d1 ∘ d2) = (↓d t i d1) ∘ (↓d t i d2)
  ↓d t i (d < τ >) = (↓d t i d) < τ >
  ↓d t i (d ⟨ τ1 ⇒ τ2 ⟩) = (↓d t i d) ⟨ τ1 ⇒ τ2 ⟩
  ↓d t i (d ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩) = (↓d t i d) ⟨ τ1 ⇒⦇-⦈⇏ τ3 ⟩

  ↓td : (t i : Nat) → ihexp → ihexp 
  ↓td t i c = c
  ↓td t i (X x) = X x
  ↓td t i (·λ[ τ ] d) = ·λ[ ↓ t i τ ] (↓td t i d)
  ↓td t i (·Λ d) = ·Λ (↓td (1+ t) i d)
  ↓td t i ⦇-⦈⟨ τ ⟩ = ⦇-⦈⟨ ↓ t i τ ⟩
  ↓td t i ⦇⌜ d ⌟⦈⟨ τ ⟩ = ⦇⌜ (↓td t i d) ⌟⦈⟨ ↓ t i τ ⟩
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
  TTSub : Nat → htyp → htyp → htyp 
  TTSub n τ1 τ2 = ↓ n 1 (TT[ (↑ Z (1+ n) τ1) / n ] τ2)

  infixl 21 TT[_/_]_

  -- substitution of types in contexts
  ctx[_/_]_ : htyp → Nat → ctx → ctx
  ctx[ τ / a ] ∅ = ∅
  ctx[ τ / a ] (τ' , Γ) = (TT[ τ / a ] τ') , (ctx[ τ / a ] Γ) 
  
  -- substitution of types in terms 
  Tt[_/_]_ : htyp → Nat → ihexp → ihexp
  Tt[ τ / t ] c = c
  Tt[ τ / t ] (X x) = X x
  Tt[ τ / t ] (·λ[ τx ] d) = ·λ[ TT[ τ / t ] τx ] (Tt[ τ / t ] d)
  Tt[ τ / t ] (·Λ d) = ·Λ (Tt[ (↑ Z 1 τ) / 1+ t ] d) 
  Tt[ τ / t ] (⦇-⦈⟨ τ' ⟩) = ⦇-⦈⟨ TT[ τ / t ] τ' ⟩
  Tt[ τ / t ] (⦇⌜ d ⌟⦈⟨  τ' ⟩) = ⦇⌜ (Tt[ τ / t ] d) ⌟⦈⟨ TT[ τ / t ] τ' ⟩
  Tt[ τ / t ] (d1 ∘ d2) = (Tt[ τ / t ] d1) ∘ (Tt[ τ / t ] d2)
  Tt[ τ / t ] (d < τ' >) = (Tt[ τ / t ] d) < TT[ τ / t ] τ' >
  Tt[ τ / t ] (d ⟨ τ1 ⇒ τ2 ⟩ ) = (Tt[ τ / t ] d) ⟨ (TT[ τ / t ] τ1) ⇒ (TT[ τ / t ] τ2) ⟩
  Tt[ τ / t ] (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = (Tt[ τ / t ] d) ⟨ (TT[ τ / t ] τ1) ⇒⦇-⦈⇏ (TT[ τ / t ] τ2) ⟩

  TtSub : Nat → htyp → ihexp → ihexp
  TtSub n τ d = ↓td n 1 (Tt[ (↑ Z (1+ n) τ) / n ] d)

  -- substitution of terms in terms
  [_/_]_ : ihexp → Nat → ihexp → ihexp
  [ d / n ] c = c
  [ d / n ] X m with natEQ m n
  ... | Inl refl = d
  ... | Inr neq = X m
  [ d / n ] (·λ[ τ ] d') = ·λ[ τ ] ([ (↑d Z 1 d) / 1+ n ] d')
  [ d / n ] ·Λ d' = ·Λ ([ d / n ] d')
  [ d / n ] ⦇-⦈⟨ τ ⟩ = ⦇-⦈⟨ τ ⟩
  [ d / n ] ⦇⌜ d' ⌟⦈⟨ τ ⟩ =  ⦇⌜ [ d / n ] d' ⌟⦈⟨ τ ⟩
  [ d / n ] (d1 ∘ d2) = ([ d / n ] d1) ∘ ([ d / n ] d2)
  [ d / n ] (d' < τ >) = ([ d / n ] d') < τ >
  [ d / n ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / n ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / n ] (d' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = ([ d / n ] d') ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩

  ttSub : ihexp → ihexp → ihexp 
  ttSub d1 d2 = ↓d Z 1 ([ (↑d Z 1 d1) / Z ] d2)

  TCtxSub : Nat → htyp → ctx → ctx 
  TCtxSub n τ ∅ = ∅
  TCtxSub n τ (x , Γ) = ↓ n 1 (TT[ (↑ Z (1+ n) τ) / n ] x) , TCtxSub n τ Γ

  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _,_⊢_=>_ : (Θ : typctx) (Γ : ctx) (e : hexp) (τ : htyp) → Set where
      SConst : {Θ : typctx} {Γ : ctx} → 
        Θ , Γ ⊢ c => b
      SAsc : {Θ : typctx} {Γ : ctx} {e : hexp} {τ : htyp} →
        Θ ⊢ τ wf →
        Θ , Γ ⊢ e <= τ →
        Θ , Γ ⊢ (e ·: τ) => τ
      SVar : {Θ : typctx} {Γ : ctx} {τ : htyp} {n : Nat} →
        n , τ ∈ Γ →
        Θ , Γ ⊢ X n => τ
      SAp : {Θ : typctx} {Γ : ctx} {e1 e2 : hexp} {τ τ1 τ2 : htyp} →
        Θ , Γ ⊢ e1 => τ1 →
        τ1 ⊓ (⦇-⦈ ==> ⦇-⦈) == τ2 ==> τ →
        Θ , Γ ⊢ e2 <= τ2 →
        Θ , Γ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Θ : typctx} {Γ : ctx} → 
        Θ , Γ ⊢ ⦇-⦈ => ⦇-⦈
      SNEHole : {Θ : typctx} {Γ : ctx} {e : hexp} {τ : htyp} →
        Θ , Γ ⊢ e => τ →
        Θ , Γ ⊢ ⦇⌜ e ⌟⦈ => ⦇-⦈
      SLam : {Θ : typctx} {Γ : ctx} {e : hexp} {τ1 τ2 : htyp} →
        Θ ⊢ τ1 wf →
        Θ , (τ1 , Γ) ⊢ e => τ2 →
        Θ , Γ ⊢ ·λ[ τ1 ] e => τ1 ==> τ2
      STLam : {Θ : typctx} {Γ : ctx} {e : hexp} {τ : htyp} → 
        (1+ Θ) , Γ ⊢ e => τ → 
        Θ , Γ ⊢ (·Λ e) => (·∀ τ)
      STAp : {Θ : typctx} {Γ : ctx} {e : hexp} {τ1 τ2 τ3 τ4 : htyp} → 
        Θ ⊢ τ1 wf →
        Θ , Γ ⊢ e => τ2 →
        τ2 ⊓ ·∀ ⦇-⦈ == (·∀ τ3) →
        TTSub Z τ1 τ3 == τ4 →
        Θ , Γ ⊢ (e < τ1 >) => τ4

    -- analysis
    data _,_⊢_<=_ : (Θ : typctx) (Γ : ctx) (e : hexp) (τ : htyp) → Set where
      ASubsume : {Θ : typctx} {Γ : ctx} {e : hexp} {τ τ' : htyp} →
        Θ , Γ ⊢ e => τ' →
        τ ~ τ' →
        Θ , Γ ⊢ e <= τ
      ALam : {Θ : typctx} {Γ : ctx} {e : hexp} {τ τ1 τ2 : htyp} →
        τ ⊓ (⦇-⦈ ==> ⦇-⦈) == τ1 ==> τ2 →
        Θ , (τ1 , Γ) ⊢ e <= τ2 →
        Θ , Γ ⊢ (·λ e) <= τ
      ATLam : {Θ : typctx} {Γ : ctx} {e : hexp} {τ1 τ2 : htyp} → 
        τ1 ⊓ ·∀ ⦇-⦈ == (·∀ τ2) → 
        (1+ Θ) , Γ ⊢ e <= τ2 → 
        Θ , Γ ⊢ (·Λ e) <= τ1

  -- bidirectional elaboration judgements
  mutual
    -- synthesis
    data _,_⊢_⇒_~>_ : (Θ : typctx) (Γ : ctx) (e : hexp) (τ : htyp) (d : ihexp) → Set where
      ESConst : ∀{Θ Γ} → 
        Θ , Γ ⊢ c ⇒ b ~> c
      ESVar : ∀{Θ Γ x τ} → 
        x , τ ∈ Γ → 
        Θ , Γ ⊢ X x ⇒ τ ~> X x
      ESLam : ∀{Θ Γ τ1 τ2 e d} →
        Θ ⊢ τ1 wf →
        Θ , (τ1 , Γ) ⊢ e ⇒ τ2 ~> d →
        Θ , Γ ⊢ (·λ[ τ1 ] e) ⇒ (τ1 ==> τ2) ~> (·λ[ τ1 ] d)
      ESTLam : ∀{Θ Γ e τ d} → 
        (1+ Θ) , Γ ⊢ e ⇒ τ ~> d → 
        Θ , Γ ⊢ (·Λ e) ⇒ (·∀ τ) ~> (·Λ d)
      ESAp : ∀{Θ Γ e1 τ τ1 τ1' τ2 τ2' d1  e2 d2 } →
        Θ , Γ ⊢ e1 => τ1 →
        τ1 ⊓ (⦇-⦈ ==> ⦇-⦈) == τ2 ==> τ →
        Θ , Γ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' →
        Θ , Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' →
        Θ , Γ ⊢ (e1 ∘ e2) ⇒ τ ~> ((d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩))
      ESTAp : ∀{Θ Γ e τ1 τ2 τ3 τ4 τ2' d} →
        Θ ⊢ τ1 wf →
        Θ , Γ ⊢ e => τ2 →
        τ2 ⊓ ·∀ ⦇-⦈ == (·∀ τ3) →
        Θ , Γ ⊢ e ⇐ (·∀ τ3) ~> d :: τ2' →
        TTSub Z τ1 τ3 == τ4 →
        Θ , Γ ⊢ (e < τ1 >) ⇒ τ4 ~> ((d ⟨ τ2' ⇒ (·∀ τ3)⟩) < τ1 >)
      ESEHole : ∀{Θ Γ} →
        Θ , Γ ⊢ ⦇-⦈ ⇒ ⦇-⦈ ~> ⦇-⦈⟨ ⦇-⦈ ⟩
      ESNEHole : ∀{Θ Γ e τ d} →
        Θ , Γ ⊢ e ⇒ τ ~> d →
        Θ , Γ ⊢ ⦇⌜ e ⌟⦈ ⇒ ⦇-⦈ ~> ⦇⌜ d ⌟⦈⟨ ⦇-⦈ ⟩
      ESAsc : ∀ {Θ Γ e τ d τ'} →
        Θ ⊢ τ wf →
        Θ , Γ ⊢ e ⇐ τ ~> d :: τ' →
        Θ , Γ ⊢ (e ·: τ) ⇒ τ ~> (d ⟨ τ' ⇒ τ ⟩)

    -- analysis
    data _,_⊢_⇐_~>_::_ : (Θ : typctx) (Γ : ctx) (e : hexp) (τ : htyp) (d : ihexp) (τ' : htyp) → Set where
      EALam : ∀{Θ Γ τ τ1 τ2 e d τ2'} →
        τ ⊓ (⦇-⦈ ==> ⦇-⦈) == τ1 ==> τ2 →
        Θ , (τ1 , Γ) ⊢ e ⇐ τ2 ~> d :: τ2' →
        Θ , Γ ⊢ ·λ e ⇐ τ ~> ·λ[ τ1 ] d :: τ1 ==> τ2'
      EATLam : ∀{Θ Γ e τ1 τ2 τ2' d} → 
        (e ≠ ⦇-⦈) →
        ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈) →
        τ1 ⊓ ·∀ ⦇-⦈ == (·∀ τ2) → 
        (1+ Θ) , Γ ⊢ e ⇐ τ2 ~> d :: τ2' →
        Θ , Γ ⊢ (·Λ e) ⇐ τ1 ~> (·Λ d) :: (·∀ τ2')
      EASubsume : ∀{e Θ Γ τ1 τ2 τ3 d} →
        (e ≠ ⦇-⦈) →
        ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈) →
        Θ , Γ ⊢ e ⇒ τ2 ~> d →
        τ1 ⊓ τ2 == τ3 →
        Θ , Γ ⊢ e ⇐ τ1 ~> (d ⟨ τ2 ⇒ τ3 ⟩) :: τ3
      EAEHole : ∀{Θ Γ τ} →
        Θ , Γ ⊢ ⦇-⦈ ⇐ τ ~> ⦇-⦈⟨ τ ⟩ :: τ
      EANEHole : ∀{Θ Γ e τ d τ'} →
        Θ , Γ ⊢ e ⇒ τ' ~> d →
        Θ , Γ ⊢ ⦇⌜ e ⌟⦈ ⇐ τ ~> ⦇⌜ d ⌟⦈⟨ τ ⟩ :: τ

  -- type assignment
  data _,_⊢_::_ : (Θ : typctx) (Γ : ctx) (d : ihexp) (τ : htyp) → Set where
    TAConst : ∀{Θ Γ} → 
      Θ , Γ ⊢ c :: b
    TAVar : ∀{Θ Γ n τ} → 
      n , τ ∈ Γ → 
      Θ , Γ ⊢ X n :: τ
    TALam : ∀{ Θ Γ τ1 d τ2} →
      Θ ⊢ τ1 wf →
      Θ , (τ1 , Γ) ⊢ d :: τ2 →
      Θ , Γ ⊢ ·λ[ τ1 ] d :: (τ1 ==> τ2)
    TATLam : ∀{ Θ Γ d τ} →
      (1+ Θ) , Γ ⊢ d :: τ →
      Θ , Γ ⊢ ·Λ d :: (·∀ τ)
    TAAp : ∀{Θ Γ d1 d2 τ1 τ} →
      Θ , Γ ⊢ d1 :: τ1 ==> τ →
      Θ , Γ ⊢ d2 :: τ1 →
      Θ , Γ ⊢ d1 ∘ d2 :: τ
    TATAp : ∀ {Θ Γ d τ1 τ2 τ3} → 
      Θ ⊢ τ1 wf →
      Θ , Γ ⊢ d :: (·∀ τ2) →
      TTSub Z τ1 τ2 == τ3 → 
      Θ , Γ ⊢ (d < τ1 >) :: τ3
    TAEHole : ∀{Θ Γ τ} →
      Θ ⊢ τ wf →
      Θ , Γ ⊢ ⦇-⦈⟨ τ ⟩ :: τ
    TANEHole : ∀ {Θ Γ d τ τ'} →
      Θ ⊢ τ wf →
      Θ , Γ ⊢ d :: τ' →
      Θ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ τ ⟩ :: τ
    TACast : ∀{Θ Γ d τ1 τ2} →
      Θ , Γ ⊢ d :: τ1 →
      Θ ⊢ τ2 wf →
      τ1 ~ τ2 →
      Θ , Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
    TAFailedCast : ∀{Θ Γ d τ1 τ2} →
      Θ , Γ ⊢ d :: τ1 →
      τ1 ground →
      τ2 ground →
      τ1 ~̸ τ2 →
      Θ , Γ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ :: τ2

  -- precision for internal expressions
  -- see Refined Criteria for Gradual Typing, Figure 9
  data _,_,_⊢_⊑i_ : (Θ : typctx) → (Γ : ctx) → (Γ' : ctx) → (d1 d2 : ihexp) → Set where
    PIConst : ∀{Θ Γ Γ'} → Θ , Γ , Γ' ⊢ c ⊑i c
    PIVar : ∀{Θ Γ Γ' n} → Θ , Γ , Γ' ⊢ (X n) ⊑i (X n) 
    PIEHole : ∀{Θ Γ Γ' τ1 τ2 d} → (Θ , Γ ⊢ d :: τ1) → (τ1 ⊑t τ2) → Θ , Γ , Γ' ⊢ d ⊑i ⦇-⦈⟨ τ2 ⟩
    PILam : ∀{Θ Γ Γ' d1 d2 τ1 τ2} → Θ , (τ1 , Γ) , (τ2 , Γ') ⊢ d1 ⊑i d2 → τ1 ⊑t τ2 → Θ , Γ , Γ' ⊢ (·λ[ τ1 ] d1) ⊑i (·λ[ τ2 ] d2)
    PITLam : ∀{Θ Γ Γ' d1 d2} → (1+ Θ) , Γ , Γ' ⊢ d1 ⊑i d2 → Θ , Γ , Γ' ⊢ (·Λ d1) ⊑i (·Λ d2)
    PINEHole : ∀{Θ Γ Γ' τ1 τ2 d1 d2} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ2 → Θ , Γ , Γ' ⊢ (⦇⌜ d1 ⌟⦈⟨ τ1 ⟩) ⊑i (⦇⌜ d2 ⌟⦈⟨ τ2 ⟩)
    PIAp :  ∀{Θ Γ Γ' d1 d2 d3 d4} → Θ , Γ , Γ' ⊢ d1 ⊑i d3 → Θ , Γ , Γ' ⊢ d2 ⊑i d4 → Θ , Γ , Γ' ⊢ (d1 ∘ d2) ⊑i (d3 ∘ d4)
    PITAp : ∀{Θ Γ Γ' d1 d2 τ1 τ2} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ2 → Θ , Γ , Γ' ⊢ (d1 < τ1 >) ⊑i (d2 < τ2 >)
    PICast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ3 τ4} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ3 → τ2 ⊑t τ4 → Θ , Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒ τ4 ⟩)
    PIFailedCast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ3 τ4} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ3 → τ2 ⊑t τ4 → Θ , Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒⦇-⦈⇏ τ4 ⟩)
    PIRemoveCast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ} → (Θ , Γ , Γ' ⊢ d1 ⊑i d2) → (Θ , Γ' ⊢ d2 :: τ) → (τ1 ⊑t τ) → (τ2 ⊑t τ) → Θ , Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒ τ2 ⟩) ⊑i d2 
    PIAddCast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ} → (Θ , Γ , Γ' ⊢ d1 ⊑i d2) → (Θ , Γ ⊢ d1 :: τ) → (τ ⊑t τ1) → (τ ⊑t τ2) → Θ , Γ , Γ' ⊢ d1 ⊑i (d2 ⟨ τ1 ⇒ τ2 ⟩) 
    PIBlame : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ} → (Θ , Γ' ⊢ d2 :: τ) → (τ2 ⊑t τ) → (Θ , Γ , Γ' ⊢ d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ⊑i d2)

  -- evaluation contexts
  data ectx : Set where
    ⊙ : ectx
    _∘₁_ : ectx → ihexp → ectx
    _∘₂_ : ihexp → ectx → ectx
    _<_> : ectx → htyp → ectx
    ⦇⌜_⌟⦈⟨_⟩ : ectx → htyp → ectx
    _⟨_⇒_⟩ : ectx → htyp → htyp → ectx
    _⟨_⇒⦇-⦈⇏_⟩ : ectx → htyp → htyp → ectx

  -- d is the result of filling the hole in ε with d'
  data _==_⟦_⟧ : (d : ihexp) (ε : ectx) (d' : ihexp) → Set where
    FHOuter : ∀{d} → d == ⊙ ⟦ d ⟧
    FHAp1 : ∀{d1 d1' d2 ε} →
           d1 == ε ⟦ d1' ⟧ →  
           (d1 ∘ d2) == (ε ∘₁ d2) ⟦ d1' ⟧
    FHAp2 : ∀{d1 d2 d2' ε} →
           -- d1 final → -- red brackets
           d2 == ε ⟦ d2' ⟧ →
           (d1 ∘ d2) == (d1 ∘₂ ε) ⟦ d2' ⟧
    FHTAp : ∀{d d' t ε} →
           d == ε ⟦ d' ⟧ →
           (d < t >) == (ε < t >) ⟦ d' ⟧
    FHNEHole : ∀{ d d' ε τ} →
              d == ε ⟦ d' ⟧ →
              ⦇⌜ d ⌟⦈⟨ τ ⟩ ==  ⦇⌜ ε ⌟⦈⟨ τ ⟩ ⟦ d' ⟧
    FHCast : ∀{ d d' ε τ1 τ2 } →
            d == ε ⟦ d' ⟧ →
            d ⟨ τ1 ⇒ τ2 ⟩ == ε ⟨ τ1 ⇒ τ2 ⟩ ⟦ d' ⟧
    FHFailedCast : ∀{ d d' ε τ1 τ2} →
            d == ε ⟦ d' ⟧ →
            (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) == (ε ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⟦ d' ⟧

  -- instruction transition judgement
  data _→>_ : (d d' : ihexp) → Set where
    ITLam : ∀{ τ d1 d2 } →
            -- d2 final → -- red brackets
            ((·λ[ τ ] d1) ∘ d2) →> (ttSub d2 d1)
    ITTLam : ∀{ d τ } →
              ((·Λ d) < τ >) →> (TtSub Z τ d)
    ITCastID : ∀{ d τ } →
               -- d final → -- red brackets
               (d ⟨ τ ⇒ τ ⟩) →> d
    ITCastSucceed : ∀{ d τ } →
                    -- d final → -- red brackets
                    τ ground →
                    (d ⟨ τ ⇒ ⦇-⦈ ⇒ τ ⟩) →> d
    ITCastFail : ∀{ d τ1 τ2} →
                 -- d final → -- red brackets
                 τ1 ground →
                 τ2 ground →
                 τ1 ~̸  τ2 →
                 (d ⟨ τ1 ⇒ ⦇-⦈ ⇒ τ2 ⟩) →> (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
    ITApCast : ∀{d1 d2 τ1 τ2 τ1' τ2' } →
               -- d1 final → -- red brackets
               -- d2 final → -- red brackets
               ((d1 ⟨ (τ1 ==> τ2) ⇒ (τ1' ==> τ2')⟩) ∘ d2) →> ((d1 ∘ (d2 ⟨ τ1' ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ2' ⟩)
    ITTApCast : ∀{ d τ1 τ2 τ3 } →
               -- d final → -- red brackets
               --  ·∀ τ ≠ ·∀ τ' →
                 ((d ⟨ (·∀ τ1) ⇒ (·∀ τ2)⟩) < τ3 >) →> ((d < τ3 >)⟨ TTSub Z τ3 τ1 ⇒ TTSub Z τ3 τ2 ⟩)
    ITGround : ∀{ d τ τ'} →
               -- d final → -- red brackets
               τ ▸gnd τ' →
               (d ⟨ τ ⇒ ⦇-⦈ ⟩) →> (d ⟨ τ ⇒ τ' ⇒ ⦇-⦈ ⟩)
    ITExpand : ∀{ d τ τ' } →
               -- d final → -- red brackets
               τ ▸gnd τ' →
               (d ⟨ ⦇-⦈ ⇒ τ ⟩) →> (d ⟨ ⦇-⦈ ⇒ τ' ⇒ τ ⟩)

  -- single step (in contextual evaluation sense)
  data _↦_ : (d d' : ihexp) → Set where
    Step : ∀{ d d0 d' d0' ε} →
           d == ε ⟦ d0 ⟧ →
           d0 →> d0' →
           d' == ε ⟦ d0' ⟧ →
           d ↦ d'

  -- reflexive transitive closure of single steps into multi steps
  data _↦*_ : (d d' : ihexp) → Set where
    MSRefl : ∀{d} → d ↦* d
    MSStep : ∀{d d' d''} →
                 d ↦ d' →
                 d' ↦* d'' →
                 d  ↦* d''

  -- -- those types without holes
  -- data _tcomplete : htyp → Set where
  --   TCBase : b tcomplete
  --   TCVar : ∀{a} → (T a) tcomplete
  --   TCArr : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ==> τ2) tcomplete
  --   TCForall : ∀{t e} → e tcomplete → (·∀ t e) tcomplete 

  -- -- those external expressions without holes
  -- data _ecomplete : hexp → Set where
  --   ECConst : c ecomplete
  --   ECAsc : ∀{τ e} → τ tcomplete → e ecomplete → (e ·: τ) ecomplete
  --   ECVar : ∀{x} → (X x) ecomplete
  --   ECLam1 : ∀{x e} → e ecomplete → (·λ x e) ecomplete
  --   ECLam2 : ∀{x e τ} → e ecomplete → τ tcomplete → (·λ x [ τ ] e) ecomplete
  --   ECTLam : ∀{t e} → e ecomplete → (·Λ t e) ecomplete
  --   ECAp : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
  --   ECTAp : ∀{τ e} → τ tcomplete → e ecomplete → (e < τ >) ecomplete

  -- -- those internal expressions without holes
  -- data _dcomplete : ihexp → Set where
  --   DCVar : ∀{x} → (X x) dcomplete
  --   DCConst : c dcomplete
  --   DCLam : ∀{x τ d} → d dcomplete → τ tcomplete → (·λ x [ τ ] d) dcomplete
  --   DCTLam : ∀{t d} → d dcomplete → (·Λ t d) dcomplete
  --   DCAp : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → (d1 ∘ d2) dcomplete
  --   DCTAp : ∀{τ d} → τ tcomplete → d dcomplete → (d < τ >) dcomplete
  --   DCCast : ∀{d τ1 τ2} → d dcomplete → τ1 tcomplete → τ2 tcomplete → (d ⟨ τ1 ⇒ τ2 ⟩) dcomplete

  -- -- contexts that only produce complete types
  -- _gcomplete : ctx → Set
  -- Γ gcomplete = (x : Nat) (τ : htyp) → (x , τ) ∈ Γ → τ tcomplete

  -- -- those internal expressions where every cast is the identity cast and
  -- -- there are no failed casts
  -- data cast-id : ihexp → Set where
  --   CIConst  : cast-id c
  --   CIVar    : ∀{x} → cast-id (X x)
  --   CILam    : ∀{x τ d} → cast-id d → cast-id (·λ x [ τ ] d)
  --   CITLam   : ∀{t d} → cast-id d → cast-id (·Λ t d)
  --   CIHole   : ∀{τ} → cast-id (⦇-⦈⟨ τ ⟩)
  --   CINEHole : ∀{d τ} → cast-id d → cast-id (⦇⌜ d ⌟⦈⟨ τ ⟩)
  --   CIAp     : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ∘ d2)
  --   CITap    : ∀{τ d} → cast-id d → cast-id (d < τ >)
  --   CICast   : ∀{d τ} → cast-id d → cast-id (d ⟨ τ ⇒ τ ⟩)
