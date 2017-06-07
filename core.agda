open import Nat
open import Prelude

module core where
  -- types
  data τ̇ : Set where
    num   : τ̇
    ⦇⦈    : τ̇
    _==>_ : τ̇ → τ̇ → τ̇
    _⊕_   : τ̇ → τ̇ → τ̇
    _⊗_   : τ̇ → τ̇ → τ̇

  -- expressions
  data ė : Set where
    _·:_   : ė → τ̇ → ė
    X      : Nat → ė
    ·λ     : Nat → ė → ė
    N      : Nat → ė
    _·+_   : ė → ė → ė
    ⦇⦈[_]  : Nat → ė
    ⦇_⦈[_] : ė → Nat → ė
    _∘_    : ė → ė → ė
    inl    : ė → ė
    inr    : ė → ė
    case   : ė → Nat → ė → Nat → ė → ė
    [_,_]  : ė → ė → ė
    fst    : ė → ė
    snd    : ė → ė

  data subst : Set where -- todo

  -- expressions without ascriptions but with casts
  data ë : Set where
    X        : Nat → ë
    ·λ       : Nat → ë → ë
    N        : Nat → ë
    _·+_     : ë → ë → ë
    ⦇⦈[_,_]  : Nat → subst → ë
    ⦇_⦈[_,_] : ë → Nat → subst → ë
    _∘_      : ë → ë → ë
    inl      : ë → ë
    inr      : ë → ë
    case     : ë → Nat → ë → Nat → ë → ë
    [_,_]    : ë → ë → ë
    fst      : ë → ë
    snd      : ë → ë
    <_>_     : ë → τ̇ → ë

  -- type consistency
  data _~_ : (t1 : τ̇) → (t2 : τ̇) → Set where
    TCRefl : {t : τ̇} → t ~ t
    TCHole1 : {t : τ̇} → t ~ ⦇⦈
    TCHole2 : {t : τ̇} → ⦇⦈ ~ t
    TCArr : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ==> t2) ~ (t1' ==> t2')
    TCSum : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ⊕ t2) ~ (t1' ⊕ t2')
    TCPro : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ⊗ t2) ~ (t1' ⊗ t2')

  -- type inconsistency
  data _~̸_ : τ̇ → τ̇ → Set where
    ICNumArr1 : {t1 t2 : τ̇} → num ~̸ (t1 ==> t2)
    ICNumArr2 : {t1 t2 : τ̇} → (t1 ==> t2) ~̸ num
    ICArr1 : {t1 t2 t3 t4 : τ̇} →
               t1 ~̸ t3 →
               (t1 ==> t2) ~̸ (t3 ==> t4)
    ICArr2 : {t1 t2 t3 t4 : τ̇} →
               t2 ~̸ t4 →
               (t1 ==> t2) ~̸ (t3 ==> t4)

    ICNumSum1 : {t1 t2 : τ̇} → num ~̸ (t1 ⊕ t2)
    ICNumSum2 : {t1 t2 : τ̇} → (t1 ⊕ t2) ~̸ num
    ICSum1 : {t1 t2 t3 t4 : τ̇} →
               t1 ~̸ t3 →
               (t1 ⊕ t2) ~̸ (t3 ⊕ t4)
    ICSum2 : {t1 t2 t3 t4 : τ̇} →
               t2 ~̸ t4 →
               (t1 ⊕ t2) ~̸ (t3 ⊕ t4)
    ICSumArr1 : {t1 t2 t3 t4 : τ̇} → (t1 ⊕ t2) ~̸ (t3 ==> t4)
    ICSumArr2 : {t1 t2 t3 t4 : τ̇} → (t1 ==> t2) ~̸ (t3 ⊕ t4)

    ICNumPro1 : {t1 t2 : τ̇} → num ~̸ (t1 ⊗ t2)
    ICNumPro2 : {t1 t2 : τ̇} → (t1 ⊗ t2) ~̸ num
    ICPro1 : {t1 t2 t3 t4 : τ̇} →
               t1 ~̸ t3 →
               (t1 ⊗ t2) ~̸ (t3 ⊗ t4)
    ICPro2 : {t1 t2 t3 t4 : τ̇} →
               t2 ~̸ t4 →
               (t1 ⊗ t2) ~̸ (t3 ⊗ t4)
    ICProArr1 : {t1 t2 t3 t4 : τ̇} → (t1 ⊗ t2) ~̸ (t3 ==> t4)
    ICProArr2 : {t1 t2 t3 t4 : τ̇} → (t1 ==> t2) ~̸ (t3 ⊗ t4)

    ICProSum1 : {t1 t2 t3 t4 : τ̇} → (t1 ⊗ t2) ~̸ (t3 ⊕ t4)
    ICProSum2 : {t1 t2 t3 t4 : τ̇} → (t1 ⊕ t2) ~̸ (t3 ⊗ t4)


  --- matching for arrows, sums, and products
  data _▸arr_ : τ̇ → τ̇ → Set where
    MAHole : ⦇⦈ ▸arr (⦇⦈ ==> ⦇⦈)
    MAArr  : {t1 t2 : τ̇} → (t1 ==> t2) ▸arr (t1 ==> t2)

  data _▸sum_ : τ̇ → τ̇ → Set where
    MSHole  : ⦇⦈ ▸sum (⦇⦈ ⊕ ⦇⦈)
    MSPlus  : {t1 t2 : τ̇} → (t1 ⊕ t2) ▸sum (t1 ⊕ t2)

  data _▸pro_ : τ̇ → τ̇ → Set where
    MPHole  : ⦇⦈ ▸pro (⦇⦈ ⊗ ⦇⦈)
    MPPlus  : {t1 t2 : τ̇} → (t1 ⊗ t2) ▸pro (t1 ⊗ t2)


  ---- contexts

  -- variables are named with naturals in ė. therefore we represent
  -- contexts as functions from names for variables (nats) to possible
  -- bindings.
  ·ctx : Set
  ·ctx = Nat → Maybe τ̇

  -- convenient shorthand for the (unique up to fun. ext.) empty context
  ∅ : ·ctx
  ∅ _ = None

  -- add a new binding to the context, clobbering anything that might have
  -- been there before.
  _,,_ : ·ctx → (Nat × τ̇) → ·ctx
  (Γ ,, (x , t)) y with natEQ x y
  (Γ ,, (x , t)) .x | Inl refl = Some t
  (Γ ,, (x , t)) y  | Inr neq  = Γ y

  -- membership, or presence, in a context
  _∈_ : (p : Nat × τ̇) → (Γ : ·ctx) → Set
  (x , t) ∈ Γ = (Γ x) == Some t

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : (n : Nat) → (Γ : ·ctx) → Set
  x # Γ = (Γ x) == None

  -- without: remove a variable from a context
  _/_ : ·ctx → Nat → ·ctx
  (Γ / x) y with natEQ x y
  (Γ / x) .x | Inl refl = None
  (Γ / x) y  | Inr neq  = Γ y

  -- bidirectional type checking judgements for ė
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
      SAsc    : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 Γ ⊢ e <= t →
                 Γ ⊢ (e ·: t) => t
      SVar    : {Γ : ·ctx} {t : τ̇} {n : Nat} →
                 (n , t) ∈ Γ →
                 Γ ⊢ X n => t
      SAp     : {Γ : ·ctx} {e1 e2 : ė} {t t' t2 : τ̇} →
                 Γ ⊢ e1 => t →
                 t ▸arr (t2 ==> t') →
                 Γ ⊢ e2 <= t2 →
                 Γ ⊢ (e1 ∘ e2) => t'
      SNum    :  {Γ : ·ctx} {n : Nat} →
                 Γ ⊢ N n => num
      SPlus   : {Γ : ·ctx} {e1 e2 : ė}  →
                 Γ ⊢ e1 <= num →
                 Γ ⊢ e2 <= num →
                 Γ ⊢ (e1 ·+ e2) => num
      SEHole  : {Γ : ·ctx} {u : Nat} → Γ ⊢ ⦇⦈[ u ] => ⦇⦈ -- todo: uniqueness of n?
      SNEHole : {Γ : ·ctx} {e : ė} {t : τ̇} {u : Nat} → -- todo: uniqueness of n?
                 Γ ⊢ e => t →
                 Γ ⊢ ⦇ e ⦈[ u ] => ⦇⦈

    --todo: add rules for products

    -- analysis
    data _⊢_<=_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
      ASubsume : {Γ : ·ctx} {e : ė} {t t' : τ̇} →
                 Γ ⊢ e => t' →
                 t ~ t' →
                 Γ ⊢ e <= t
      ALam : {Γ : ·ctx} {e : ė} {t t1 t2 : τ̇} {x : Nat} →
                 x # Γ →
                 t ▸arr (t1 ==> t2) →
                 (Γ ,, (x , t1)) ⊢ e <= t2 →
                 Γ ⊢ (·λ x e) <= t
      AInl : {Γ : ·ctx} {e : ė} {t+ t1 t2 : τ̇} →
                 t+ ▸sum (t1 ⊕ t2) →
                 Γ ⊢ e <= t1 →
                 Γ ⊢ inl e <= t+
      AInr : {Γ : ·ctx} {e : ė} {t+ t1 t2 : τ̇} →
                 t+ ▸sum (t1 ⊕ t2) →
                 Γ ⊢ e <= t2 →
                 Γ ⊢ inr e <= t+
      ACase : {Γ : ·ctx} {e e1 e2 : ė} {t t+ t1 t2 : τ̇} {x y : Nat} →
                 x # Γ →
                 y # Γ →
                 t+ ▸sum (t1 ⊕ t2) →
                 Γ ⊢ e => t+ →
                 (Γ ,, (x , t1)) ⊢ e1 <= t →
                 (Γ ,, (y , t2)) ⊢ e2 <= t →
                 Γ ⊢ case e x e1 y e2 <= t



  -- those types without holes anywhere
  tcomplete : τ̇ → Set
  tcomplete num         = ⊤
  tcomplete ⦇⦈        = ⊥
  tcomplete (t1 ==> t2) = tcomplete t1 × tcomplete t2
  tcomplete (t1 ⊕ t2)   = tcomplete t1 × tcomplete t2
  tcomplete (t1 ⊗ t2)   = tcomplete t1 × tcomplete t2

  -- those expressions without holes anywhere
  ecomplete : ė → Set
  ecomplete (e1 ·: t)  = ecomplete e1 × tcomplete t
  ecomplete (X _)      = ⊤
  ecomplete (·λ _ e1)  = ecomplete e1
  ecomplete (N x)      = ⊤
  ecomplete (e1 ·+ e2) = ecomplete e1 × ecomplete e2
  ecomplete ⦇⦈[ u ]       = ⊥
  ecomplete ⦇ e1 ⦈[ u ]   = ⊥
  ecomplete (e1 ∘ e2)  = ecomplete e1 × ecomplete e2
  ecomplete (inl e)    = ecomplete e
  ecomplete (inr e)    = ecomplete e
  ecomplete (case e x e1 y e2)  = ecomplete e × ecomplete e1 × ecomplete e2
  ecomplete [ e1 , e2 ] = ecomplete e1 × ecomplete e2
  ecomplete (fst e) = ecomplete e
  ecomplete (snd e) = ecomplete e

  -- expansion
  mutual
    data _⊢_⇒_~>_⊣_ : (Γ : ·ctx) (e : ė) (t : τ̇) (e' : ë) (Δ : ·ctx) → Set where

    data _⊢_⇐_~>_::_⊣_ : (Γ : ·ctx) (e : ė) (t : τ̇) (e' : ë) (t' : τ̇)(Δ : ·ctx) → Set where

  -- type assignment
  data _,_⊢_::_ : (Γ : ·ctx) (Δ : ·ctx) (e' : ë) (t : τ̇) → Set where

  -- value
  data _val : ë → Set where

  -- indeterminate
  data _indet : ë → Set where

  -- error
  data _err[_] : ë → ·ctx → Set where -- todo not a context

  -- final
  data _final : ë → Set where

  -- small step semantics
  data _↦_ : ë → ë → Set where
