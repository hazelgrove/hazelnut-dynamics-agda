open import Nat
open import Prelude
open import contexts

module core where
  -- types
  data τ̇ : Set where
    b     : τ̇
    ⦇⦈    : τ̇
    _==>_ : τ̇ → τ̇ → τ̇

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  -- expressions
  data ė : Set where
    c       : ė
    _·:_    : ė → τ̇ → ė
    X       : Nat → ė
    ·λ      : Nat → ė → ė
    ·λ_[_]_ : Nat → τ̇ → ė → ė
    ⦇⦈[_]   : Nat → ė
    ⦇_⦈[_]  : ė → Nat → ė
    _∘_     : ė → ė → ė

  subst : Set -- todo: no idea if this is right
  subst = ė ctx

  -- expressions without ascriptions but with casts
  data ë : Set where
    c        : ë
    X        : Nat → ë
    ·λ_[_]_  : Nat → τ̇ → ë → ë
    ⦇⦈[_]    : (Nat × subst) → ë
    ⦇_⦈[_]   : ë → (Nat × subst) → ë
    _∘_      : ë → ë → ë
    <_>_     : ë → τ̇ → ë

  -- type consistency
  data _~_ : (t1 : τ̇) → (t2 : τ̇) → Set where
    TCRefl : {t : τ̇} → t ~ t
    TCHole1 : {t : τ̇} → t ~ ⦇⦈
    TCHole2 : {t : τ̇} → ⦇⦈ ~ t
    TCArr : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               t1 ==> t2 ~ t1' ==> t2'

  -- type inconsistency
  data _~̸_ : τ̇ → τ̇ → Set where
    ICBaseArr1 : {t1 t2 : τ̇} → b ~̸ t1 ==> t2
    ICBaseArr2 : {t1 t2 : τ̇} → t1 ==> t2 ~̸ b
    ICArr1 : {t1 t2 t3 t4 : τ̇} →
               t1 ~̸ t3 →
               t1 ==> t2 ~̸ t3 ==> t4
    ICArr2 : {t1 t2 t3 t4 : τ̇} →
               t2 ~̸ t4 →
               t1 ==> t2 ~̸ t3 ==> t4

  --- matching for arrows, sums, and products
  data _▸arr_ : τ̇ → τ̇ → Set where
    MAHole : ⦇⦈ ▸arr ⦇⦈ ==> ⦇⦈
    MAArr  : {t1 t2 : τ̇} → t1 ==> t2 ▸arr t1 ==> t2

  -- aliases for type and hole contexts
  tctx : Set
  tctx = τ̇ ctx

  hctx : Set
  hctx = (τ̇ ctx × τ̇) ctx

  postulate -- todo: write this stuff later
    id : {A : Set} → A ctx → subst
    [_]_ : subst → ë → ë

  -- this is just fancy notation to match the paper
  _::[_]_ : Nat → tctx → τ̇ → (Nat × tctx × τ̇)
  u ::[ Γ ] t = u , Γ , t


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
                 t ▸arr t2 ==> t' →
                 Γ ⊢ e2 <= t2 →
                 Γ ⊢ (e1 ∘ e2) => t'
      SEHole  : {Γ : tctx} {u : Nat} → Γ ⊢ ⦇⦈[ u ] => ⦇⦈ -- todo: uniqueness of n?
      SNEHole : {Γ : tctx} {e : ė} {t : τ̇} {u : Nat} → -- todo: uniqueness of n?
                 Γ ⊢ e => t →
                 Γ ⊢ ⦇ e ⦈[ u ] => ⦇⦈
      SLam    : {Γ : tctx} {e : ė} {t1 t2 : τ̇} {x : Nat} →
                 x # Γ → -- todo
                 (Γ ,, (x , t1)) ⊢ e => t2 →
                 Γ ⊢ ·λ x [ t1 ] e => t1 ==> t2

    -- analysis
    data _⊢_<=_ : (Γ : τ̇ ctx) → (e : ė) → (t : τ̇) → Set where
      ASubsume : {Γ : tctx} {e : ė} {t t' : τ̇} →
                 Γ ⊢ e => t' →
                 t ~ t' →
                 Γ ⊢ e <= t
      ALam : {Γ : tctx} {e : ė} {t t1 t2 : τ̇} {x : Nat} →
                 x # Γ →
                 t ▸arr t1 ==> t2 →
                 (Γ ,, (x , t1)) ⊢ e <= t2 →
                 Γ ⊢ (·λ x e) <= t

  -- todo: do we care about completeness of ė or e-umlauts?
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
  ecomplete (·λ x [ t ] e) = tcomplete t × ecomplete e

  -- expansion
  mutual
    data _⊢_⇒_~>_⊣_ : (Γ : tctx) (e : ė) (t : τ̇) (e' : ë) (Δ : hctx) → Set where
      ESConst : ∀{Γ} → Γ ⊢ c ⇒ b ~> c ⊣ ∅
      ESVar   : ∀{Γ x t} → (Γ ,, (x , t)) ⊢ X x ⇒ t ~> X x ⊣ ∅
      ESLam   : ∀{Γ x t1 t2 e e' Δ } →
                     (Γ ,, (x , t1)) ⊢ e ⇒ t2 ~> e' ⊣ Δ →
                      Γ ⊢ ·λ x [ t1 ] e ⇒ (t1 ==> t2) ~> ·λ x [ t1 ] e' ⊣ ∅

      -- todo: really ought to check disjointness of domains here ..
      ESAp1   : ∀{Γ e1 e2 e2' e1' Δ1 t2 t1 Δ2} →
                Γ ⊢ e1 => ⦇⦈ →
                Γ ⊢ e2 ⇐ ⦇⦈ ~> e2' :: t2 ⊣ Δ2 →
                Γ ⊢ e1 ⇐ (t2 ==> ⦇⦈) ~> e1' :: t1 ⊣ Δ1 →
                Γ ⊢ e1 ∘ e2 ⇒ ⦇⦈ ~> (< e1' > t2) ∘ e2' ⊣ (Δ1 ∪ Δ2)
      ESAp2 : ∀{Γ e1 t2 t e1' e2' Δ1 Δ2 t2' e2} →
              Γ ⊢ e1 ⇒ (t2 ==> t) ~> e1' ⊣ Δ1 →
              Γ ⊢ e2 ⇐ t2 ~> e2' :: t2' ⊣ Δ2 →
              (t2 == t2' → ⊥) →
              Γ ⊢ e1 ∘ e2 ⇒ t ~> e1' ∘ (< e2' > t2) ⊣ (Δ1 ∪ Δ2)
      ESAp3 : ∀{Γ e1 t e1' Δ1 e2 t2 e2' Δ2 } →
              Γ ⊢ e1 ⇒ (t2 ==> t) ~> e1' ⊣ Δ1 →
              Γ ⊢ e2 ⇐ t2 ~> e2' :: t2 ⊣ Δ2 →
              Γ ⊢ e1 ∘ e2 ⇒ t ~> e1' ∘ e2' ⊣ (Δ1 ∪ Δ2)
      ESEHole : ∀{ Γ u } →
                Γ ⊢ ⦇⦈[ u ] ⇒ ⦇⦈ ~> ⦇⦈[ u , id Γ ] ⊣  ⟦ u ::[ Γ ] ⦇⦈ ⟧
      ESNEHole : ∀{ Γ e t e' u Δ } →
                 Γ ⊢ e ⇒ t ~> e' ⊣ Δ →
                 Γ ⊢ ⦇ e ⦈[ u ] ⇒ ⦇⦈ ~> ⦇ e' ⦈[ u , id Γ ] ⊣ (Δ ,, u ::[ Γ ] ⦇⦈)
      ESAsc1 : ∀ {Γ e t e' t' Δ} →
                 Γ ⊢ e ⇐ t ~> e' :: t' ⊣ Δ →
                 (t == t' → ⊥) →
                 Γ ⊢ (e ·: t) ⇒ t ~> (< e' > t) ⊣ Δ
      ESAsc2 : ∀{Γ e t e' t' Δ } →
               Γ ⊢ e ⇐ t ~> e' :: t' ⊣ Δ →
               Γ ⊢ (e ·: t) ⇒ t ~> e' ⊣ Δ

    data _⊢_⇐_~>_::_⊣_ : (Γ : tctx) (e : ė) (t : τ̇) (e' : ë) (t' : τ̇)(Δ : hctx) → Set where
      EALam : ∀{Γ x t1 t2 e e' t2' Δ } →
              (Γ ,, (x , t1)) ⊢ e ⇐ t2 ~> e' :: t2' ⊣ Δ →
              Γ ⊢ ·λ x e ⇐ (t1 ==> t2) ~> ·λ x [ t1 ] e' :: (t1 ==> t2') ⊣ Δ
      EASubsume : ∀{e u m Γ t' e' Δ t} →
                  (e == ⦇⦈[ u ] → ⊥) →
                  (e == ⦇ m ⦈[ u ] → ⊥) →
                  Γ ⊢ e ⇒ t' ~> e' ⊣ Δ →
                  t ~ t' →
                  Γ ⊢ e ⇐ t ~> e' :: t' ⊣ Δ
      EAEHole : ∀{ Γ u t  } →
                Γ ⊢ ⦇⦈[ u ] ⇐ t ~> ⦇⦈[ u , id Γ ] :: t ⊣ ⟦ u ::[ Γ ] t ⟧
      EANEHole : ∀{ Γ e u t e' t' Δ  } →
                 Γ ⊢ e ⇒ t' ~> e' ⊣ Δ →
                 t ~ t' →
                 Γ ⊢ ⦇ e ⦈[ u ] ⇐ t ~> ⦇ e' ⦈[ u , id Γ ] :: t ⊣ (Δ ,, u ::[ Γ ] t)

  -- type assignment
  data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (e' : ë) (t : τ̇) → Set where
    TAConst : ∀{Δ Γ} → Δ , Γ ⊢ c :: b
    TAVar : ∀{Δ Γ x t} → Δ , (Γ ,, (x , t)) ⊢ X x :: t
    TALam : ∀{ Δ Γ x t1 e t2} →
            Δ , (Γ ,, (x , t1)) ⊢ e :: t2 →
            Δ , Γ ⊢ ·λ x [ t1 ] e :: (t1 ==> t2)
    TAAp : ∀{ Δ Γ e1 e2 t1 t2 t} →
           Δ , Γ ⊢ e1 :: t1 →
           t1 ▸arr (t2 ==> t) →
           Δ , Γ ⊢ e2 :: t2 →
           Δ , Γ ⊢ e1 ∘ e2 :: t
    -- TAEHole : ∀{ Δ Γ σ u Γ' } → -- todo: overloaded form in the paper here
    -- TANEHole : ∀ { Δ Γ e t' Γ' u σ t }
    TACast : ∀{ Δ Γ e t t'} →
           Δ , Γ ⊢ e :: t' →
           t ~ t' →
           Δ , Γ ⊢ < e > t :: t

  -- todo: substition goes here

  -- value
  data _val : ë → Set where
    VConst : c val
    VLam   : ∀{x t e} → (·λ x [ t ] e) val

  -- error
  data _err[_] : ë → hctx → Set where

  mutual
    -- indeterminate
    data _indet : ë → Set where
      IEHole : ∀{u σ} → ⦇⦈[ u , σ ] indet
      INEHole : ∀{e u σ} → e final → ⦇ e ⦈[ u , σ ] indet
      IAp : ∀{e1 e2} → e1 indet → e2 final → (e1 ∘ e2) indet
      ICast : ∀{e t} → e indet → (< e > t) indet

    -- final
    data _final : ë → Set where
      FVal : ∀{e} → e val → e final
      FIndet : ∀{e} → e indet → e final

  -- small step semantics
  data _↦_ : ë → ë → Set where
