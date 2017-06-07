open import Nat
open import Prelude
open import contexts

module core where
  -- types
  data τ̇ : Set where
    b     : τ̇
    ⦇⦈    : τ̇
    _==>_ : τ̇ → τ̇ → τ̇

  -- expressions
  data ė : Set where
    c      : ė
    _·:_   : ė → τ̇ → ė
    X      : Nat → ė
    ·λ     : Nat → ė → ė
    ⦇⦈[_]  : Nat → ė
    ⦇_⦈[_] : ė → Nat → ė
    _∘_    : ė → ė → ė

  data subst : Set where -- todo; reuse contexts? do we need access to an enumeration of the domain?

  -- expressions without ascriptions but with casts
  data ë : Set where
    X        : Nat → ë
    ·λ       : Nat → ë → ë
    ⦇⦈[_,_]  : Nat → subst → ë
    ⦇_⦈[_,_] : ë → Nat → subst → ë
    _∘_      : ë → ë → ë

  -- type consistency
  data _~_ : (t1 : τ̇) → (t2 : τ̇) → Set where
    TCRefl : {t : τ̇} → t ~ t
    TCHole1 : {t : τ̇} → t ~ ⦇⦈
    TCHole2 : {t : τ̇} → ⦇⦈ ~ t
    TCArr : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ==> t2) ~ (t1' ==> t2')

  -- type inconsistency
  data _~̸_ : τ̇ → τ̇ → Set where
    ICBaseArr1 : {t1 t2 : τ̇} → b ~̸ (t1 ==> t2)
    ICBaseArr2 : {t1 t2 : τ̇} → (t1 ==> t2) ~̸ b
    ICArr1 : {t1 t2 t3 t4 : τ̇} →
               t1 ~̸ t3 →
               (t1 ==> t2) ~̸ (t3 ==> t4)
    ICArr2 : {t1 t2 t3 t4 : τ̇} →
               t2 ~̸ t4 →
               (t1 ==> t2) ~̸ (t3 ==> t4)

  --- matching for arrows, sums, and products
  data _▸arr_ : τ̇ → τ̇ → Set where
    MAHole : ⦇⦈ ▸arr (⦇⦈ ==> ⦇⦈)
    MAArr  : {t1 t2 : τ̇} → (t1 ==> t2) ▸arr (t1 ==> t2)

  -- aliases for type and hole contexts
  tctx : Set
  tctx = τ̇ ctx

  hctx : Set
  hctx = (τ̇ ctx × τ̇) ctx

  -- bidirectional type checking judgements for ė
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : tctx) → (e : ė) → (t : τ̇) → Set where
      SConst  : {Γ : tctx} → Γ ⊢ c => b
      SAsc    : {Γ : tctx} {e : ė} {t : τ̇} →
                 Γ ⊢ e <= t →
                 Γ ⊢ (e ·: t) => t
      SVar    : {Γ : tctx} {t : τ̇} {n : Nat} →
                 (n , t) ∈ Γ →
                 Γ ⊢ X n => t
      SAp     : {Γ : tctx} {e1 e2 : ė} {t t' t2 : τ̇} →
                 Γ ⊢ e1 => t →
                 t ▸arr (t2 ==> t') →
                 Γ ⊢ e2 <= t2 →
                 Γ ⊢ (e1 ∘ e2) => t'
      SEHole  : {Γ : tctx} {u : Nat} → Γ ⊢ ⦇⦈[ u ] => ⦇⦈ -- todo: uniqueness of n?
      SNEHole : {Γ : tctx} {e : ė} {t : τ̇} {u : Nat} → -- todo: uniqueness of n?
                 Γ ⊢ e => t →
                 Γ ⊢ ⦇ e ⦈[ u ] => ⦇⦈

    -- analysis
    data _⊢_<=_ : (Γ : τ̇ ctx) → (e : ė) → (t : τ̇) → Set where
      ASubsume : {Γ : tctx} {e : ė} {t t' : τ̇} →
                 Γ ⊢ e => t' →
                 t ~ t' →
                 Γ ⊢ e <= t
      ALam : {Γ : tctx} {e : ė} {t t1 t2 : τ̇} {x : Nat} →
                 x # Γ →
                 t ▸arr (t1 ==> t2) →
                 (Γ ,, (x , t1)) ⊢ e <= t2 →
                 Γ ⊢ (·λ x e) <= t

  -- those types without holes anywhere
  tcomplete : τ̇ → Set
  tcomplete b         = ⊤
  tcomplete ⦇⦈        = ⊥
  tcomplete (t1 ==> t2) = tcomplete t1 × tcomplete t2

  -- those expressions without holes anywhere
  ecomplete : ė → Set
  ecomplete c = ⊤
  ecomplete (e1 ·: t)  = ecomplete e1 × tcomplete t
  ecomplete (X _)      = ⊤
  ecomplete (·λ _ e1)  = ecomplete e1
  ecomplete ⦇⦈[ u ]       = ⊥
  ecomplete ⦇ e1 ⦈[ u ]   = ⊥
  ecomplete (e1 ∘ e2)  = ecomplete e1 × ecomplete e2

  -- expansion
  mutual
    data _⊢_⇒_~>_⊣_ : (Γ : tctx) (e : ė) (t : τ̇) (e' : ë) (Δ : hctx) → Set where

    data _⊢_⇐_~>_::_⊣_ : (Γ : tctx) (e : ė) (t : τ̇) (e' : ë) (t' : τ̇)(Δ : hctx) → Set where

  -- type assignment
  data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (e' : ë) (t : τ̇) → Set where

  -- value
  data _val : ë → Set where

  -- indeterminate
  data _indet : ë → Set where

  -- error
  data _err[_] : ë → hctx → Set where -- todo not a context

  -- final
  data _final : ë → Set where

  -- small step semantics
  data _↦_ : ë → ë → Set where
