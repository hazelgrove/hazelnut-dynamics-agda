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

  -- expressions, prefixed with a · to distinguish name clashes with agda
  -- built-ins
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

  -- matching produces unique answers for arrows, sums, and products
  ▸arr-unicity : ∀{ t t2 t3 } →
                 t ▸arr t2 →
                 t ▸arr t3 →
                 t2 == t3
  ▸arr-unicity MAHole MAHole = refl
  ▸arr-unicity MAArr MAArr = refl

  ▸sum-unicity : ∀{ t t2 t3 } →
                 t ▸sum t2 →
                 t ▸sum t3 →
                 t2 == t3
  ▸sum-unicity MSHole MSHole = refl
  ▸sum-unicity MSPlus MSPlus = refl

  ▸pro-unicity : ∀{ t t2 t3 } →
                 t ▸pro t2 →
                 t ▸pro t3 →
                 t2 == t3
  ▸pro-unicity MPHole MPHole = refl
  ▸pro-unicity MPPlus MPPlus = refl


  -- if an arrow matches, then it's consistent with the least restrictive
  -- function type
  matchconsist : ∀{t t'} →
                 t ▸arr t' →
                 t ~ (⦇⦈ ==> ⦇⦈)
  matchconsist MAHole = TCHole2
  matchconsist MAArr = TCArr TCHole1 TCHole1

  matchnotnum : ∀{t1 t2} → num ▸arr (t1 ==> t2) → ⊥
  matchnotnum ()

  ---- contexts and some operations on them

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

  ----- some theorems about the rules and judgement presented so far.

  -- a variable is apart from any context from which it is removed
  aar : (Γ : ·ctx) (x : Nat) → x # (Γ / x)
  aar Γ x with natEQ x x
  aar Γ x | Inl refl = refl
  aar Γ x | Inr x≠x  = abort (x≠x refl)

  -- contexts give at most one binding for each variable
  ctxunicity : {Γ : ·ctx} {n : Nat} {t t' : τ̇} →
               (n , t) ∈ Γ →
               (n , t') ∈ Γ →
               t == t'
  ctxunicity {n = n} p q with natEQ n n
  ctxunicity p q | Inl refl = someinj (! p · q)
  ctxunicity _ _ | Inr x≠x = abort (x≠x refl)

  -- type consistency is symmetric
  ~sym : {t1 t2 : τ̇} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)
  ~sym (TCSum p1 p2) = TCSum (~sym p1) (~sym p2)
  ~sym (TCPro p1 p2) = TCPro (~sym p1) (~sym p2)

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : τ̇) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (num ==> num) ⦇⦈ num TCHole1 TCHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ~dec : (t1 t2 : τ̇) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇⦈ = Inl TCHole1
  ~dec ⦇⦈ _ = Inl TCHole2
    -- num cases
  ~dec num num = Inl TCRefl
  ~dec num (t2 ==> t3) = Inr ICNumArr1
    -- arrow cases
  ~dec (t1 ==> t2) num = Inr ICNumArr2
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (ICArr2 y)
  ... | Inr x | _     = Inr (ICArr1 x)
    -- plus cases
  ~dec (t1 ⊕ t2) num = Inr ICNumSum2
  ~dec (t1 ⊕ t2) (t3 ==> t4) = Inr ICSumArr1
  ~dec (t1 ⊕ t2) (t3 ⊕ t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCSum x y)
  ... | _     | Inr x = Inr (ICSum2 x)
  ... | Inr x | Inl _ = Inr (ICSum1 x)
  ~dec num (y ⊕ y₁) = Inr ICNumSum1
  ~dec (x ==> x₁) (y ⊕ y₁) = Inr ICSumArr2
  ~dec num (t2 ⊗ t3) = Inr ICNumPro1
  ~dec (t1 ==> t2) (t3 ⊗ t4) = Inr ICProArr2
  ~dec (t1 ⊕ t2) (t3 ⊗ t4) = Inr ICProSum2
  ~dec (t1 ⊗ t2) num = Inr ICNumPro2
  ~dec (t1 ⊗ t2) (t3 ==> t4) = Inr ICProArr1
  ~dec (t1 ⊗ t2) (t3 ⊕ t4) = Inr ICProSum1
  ~dec (t1 ⊗ t2) (t3 ⊗ t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCPro x y)
  ... | _     | Inr x = Inr (ICPro2 x)
  ... | Inr x | Inl _ = Inr (ICPro1 x)

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : τ̇} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart ICNumArr1 ()
  ~apart ICNumArr2 ()
  ~apart (ICArr1 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr1 x) (TCArr y y₁) = ~apart x y
  ~apart (ICArr2 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr2 x) (TCArr y y₁) = ~apart x y₁
  ~apart ICNumSum1 ()
  ~apart ICNumSum2 ()
  ~apart (ICSum1 x) TCRefl = ~apart x TCRefl
  ~apart (ICSum1 x) (TCSum y y₁) = ~apart x y
  ~apart (ICSum2 x) TCRefl = ~apart x TCRefl
  ~apart (ICSum2 x) (TCSum y y₁) = ~apart x y₁
  ~apart ICSumArr1 ()
  ~apart ICSumArr2 ()
  ~apart ICNumPro1 ()
  ~apart ICNumPro2 ()
  ~apart (ICPro1 x) TCRefl = ~apart x TCRefl
  ~apart (ICPro1 x) (TCPro y y₁) = ~apart x y
  ~apart (ICPro2 x) TCRefl = ~apart x TCRefl
  ~apart (ICPro2 x) (TCPro y y₁) = ~apart x y₁
  ~apart ICProArr1 ()
  ~apart ICProArr2 ()
  ~apart ICProSum1 ()
  ~apart ICProSum2 ()

  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic positions because we think of
  -- the type as an input
  synthunicity : {Γ : ·ctx} {e : ė} {t t' : τ̇} →
                  (Γ ⊢ e => t)
                → (Γ ⊢ e => t')
                → t == t'
  synthunicity (SAsc _) (SAsc _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp D1 MAHole b) (SAp D2 MAHole y) = refl
  synthunicity (SAp D1 MAHole b) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr b) (SAp D2 MAHole y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr b) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | refl = refl
  synthunicity SNum SNum = refl
  synthunicity (SPlus _ _ ) (SPlus _ _ ) = refl
  synthunicity SEHole SEHole = refl
  synthunicity (SNEHole _) (SNEHole _) = refl

  -- those types without holes anywhere
  tcomplete : τ̇ → Set
  tcomplete num         = ⊤
  tcomplete ⦇⦈        = ⊥
  tcomplete (t1 ==> t2) = tcomplete t1 × tcomplete t2
  tcomplete (t1 ⊕ t2)   = tcomplete t1 × tcomplete t2
  tcomplete (t1 ⊗ t2)   = tcomplete t1 × tcomplete t2

  -- similarly to the complete types, the complete expressions
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
  data _value : ë → Set where

  -- indeterminate
  data _indet : ë → Set where

  -- error
  data _err[_] : ë → ·ctx → Set where -- todo not a context

  -- final
  data _final : ë → Set where

  -- small step semantics
  data _↦_ : ë → ë → Set where
