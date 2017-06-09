open import Nat
open import Prelude
open import contexts

module core where
  -- types
  data htyp : Set where
    b     : htyp
    ⦇⦈    : htyp
    _==>_ : htyp → htyp → htyp

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  -- expressions
  data hexp : Set where
    c       : hexp
    _·:_    : hexp → htyp → hexp
    X       : Nat → hexp
    ·λ      : Nat → hexp → hexp
    ·λ_[_]_ : Nat → htyp → hexp → hexp
    ⦇⦈[_]   : Nat → hexp
    ⦇_⦈[_]  : hexp → Nat → hexp
    _∘_     : hexp → hexp → hexp

  subst : Set -- todo: no idea if this is right
  subst = hexp ctx

  -- expressions without ascriptions but with casts
  data dhexp : Set where
    c        : dhexp
    X        : Nat → dhexp
    ·λ_[_]_  : Nat → htyp → dhexp → dhexp
    ⦇⦈[_]    : (Nat × subst) → dhexp
    ⦇_⦈[_]   : dhexp → (Nat × subst) → dhexp
    _∘_      : dhexp → dhexp → dhexp
    <_>_     : htyp → dhexp → dhexp

  -- type consistency
  data _~_ : (t1 t2 : htyp) → Set where
    TCRefl  : {t : htyp} → t ~ t
    TCHole1 : {t : htyp} → t ~ ⦇⦈
    TCHole2 : {t : htyp} → ⦇⦈ ~ t
    TCArr   : {t1 t2 t1' t2' : htyp} →
               t1 ~ t1' →
               t2 ~ t2' →
               t1 ==> t2 ~ t1' ==> t2'

  -- type inconsistency
  data _~̸_ : htyp → htyp → Set where
    ICBaseArr1 : {t1 t2 : htyp} → b ~̸ t1 ==> t2
    ICBaseArr2 : {t1 t2 : htyp} → t1 ==> t2 ~̸ b
    ICArr1 : {t1 t2 t3 t4 : htyp} →
               t1 ~̸ t3 →
               t1 ==> t2 ~̸ t3 ==> t4
    ICArr2 : {t1 t2 t3 t4 : htyp} →
               t2 ~̸ t4 →
               t1 ==> t2 ~̸ t3 ==> t4

  --- matching for arrows, sums, and products
  data _▸arr_ : htyp → htyp → Set where
    MAHole : ⦇⦈ ▸arr ⦇⦈ ==> ⦇⦈
    MAArr  : {t1 t2 : htyp} → t1 ==> t2 ▸arr t1 ==> t2

  -- aliases for type and hole contexts
  tctx : Set
  tctx = htyp ctx

  hctx : Set
  hctx = (htyp ctx × htyp) ctx

  postulate -- todo: write this stuff later
    id : {A : Set} → A ctx → subst
    [_]_ : subst → dhexp → dhexp

  -- this is just fancy notation to match the paper
  _::[_]_ : Nat → tctx → htyp → (Nat × tctx × htyp)
  u ::[ Γ ] t = u , Γ , t


  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : tctx) → (e : hexp) → (t : htyp) → Set where
      SConst  : {Γ : tctx} → Γ ⊢ c => b
      SAsc    : {Γ : tctx} {e : hexp} {t : htyp} →
                 Γ ⊢ e <= t →
                 Γ ⊢ (e ·: t) => t
      SVar    : {Γ : tctx} {t : htyp} {n : Nat} →
                 (n , t) ∈ Γ →
                 Γ ⊢ X n => t
      SAp     : {Γ : tctx} {e1 e2 : hexp} {t t' t2 : htyp} →
                 Γ ⊢ e1 => t →
                 t ▸arr t2 ==> t' →
                 Γ ⊢ e2 <= t2 →
                 Γ ⊢ (e1 ∘ e2) => t'
      SEHole  : {Γ : tctx} {u : Nat} → Γ ⊢ ⦇⦈[ u ] => ⦇⦈ -- todo: uniqueness of n?
      SNEHole : {Γ : tctx} {e : hexp} {t : htyp} {u : Nat} → -- todo: uniqueness of n?
                 Γ ⊢ e => t →
                 Γ ⊢ ⦇ e ⦈[ u ] => ⦇⦈
      SLam    : {Γ : tctx} {e : hexp} {t1 t2 : htyp} {x : Nat} →
                 x # Γ → -- todo
                 (Γ ,, (x , t1)) ⊢ e => t2 →
                 Γ ⊢ ·λ x [ t1 ] e => t1 ==> t2

    -- analysis
    data _⊢_<=_ : (Γ : htyp ctx) → (e : hexp) → (t : htyp) → Set where
      ASubsume : {Γ : tctx} {e : hexp} {t t' : htyp} →
                 Γ ⊢ e => t' →
                 t ~ t' →
                 Γ ⊢ e <= t
      ALam : {Γ : tctx} {e : hexp} {t t1 t2 : htyp} {x : Nat} →
                 x # Γ →
                 t ▸arr t1 ==> t2 →
                 (Γ ,, (x , t1)) ⊢ e <= t2 →
                 Γ ⊢ (·λ x e) <= t

  -- todo: do we care about completeness of hexp or e-umlauts?
  -- those types without holes anywhere
  tcomplete : htyp → Set
  tcomplete b         = ⊤
  tcomplete ⦇⦈        = ⊥
  tcomplete (t1 ==> t2) = tcomplete t1 × tcomplete t2

  -- those expressions without holes anywhere
  ecomplete : hexp → Set
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
    data _⊢_⇒_~>_⊣_ : (Γ : tctx) (e : hexp) (t : htyp) (d : dhexp) (Δ : hctx) → Set where
      ESConst : ∀{Γ} → Γ ⊢ c ⇒ b ~> c ⊣ ∅
      ESVar   : ∀{Γ x t} → (Γ ,, (x , t)) ⊢ X x ⇒ t ~> X x ⊣ ∅
      ESLam   : ∀{Γ x t1 t2 e d Δ } →
                     (Γ ,, (x , t1)) ⊢ e ⇒ t2 ~> d ⊣ Δ →
                      Γ ⊢ ·λ x [ t1 ] e ⇒ (t1 ==> t2) ~> ·λ x [ t1 ] d ⊣ ∅

      -- todo: really ought to check disjointness of domains here ..
      ESAp1   : ∀{Γ e1 e2 d2 d1 Δ1 t2 t1 Δ2} →
                Γ ⊢ e1 => ⦇⦈ →
                Γ ⊢ e2 ⇐ ⦇⦈ ~> d2 :: t2 ⊣ Δ2 →
                Γ ⊢ e1 ⇐ (t2 ==> ⦇⦈) ~> d1 :: t1 ⊣ Δ1 →
                Γ ⊢ e1 ∘ e2 ⇒ ⦇⦈ ~> (< t2 ==> ⦇⦈ > d1) ∘ d2 ⊣ (Δ1 ∪ Δ2)
      ESAp2 : ∀{Γ e1 t2 t d1 d2 Δ1 Δ2 t2' e2} →
              Γ ⊢ e1 ⇒ (t2 ==> t) ~> d1 ⊣ Δ1 →
              Γ ⊢ e2 ⇐ t2 ~> d2 :: t2' ⊣ Δ2 →
              (t2 == t2' → ⊥) →
              Γ ⊢ e1 ∘ e2 ⇒ t ~> d1 ∘ (< t2 > d2) ⊣ (Δ1 ∪ Δ2)
      ESAp3 : ∀{Γ e1 t d1 Δ1 e2 t2 d2 Δ2 } →
              Γ ⊢ e1 ⇒ (t2 ==> t) ~> d1 ⊣ Δ1 →
              Γ ⊢ e2 ⇐ t2 ~> d2 :: t2 ⊣ Δ2 →
              Γ ⊢ e1 ∘ e2 ⇒ t ~> d1 ∘ d2 ⊣ (Δ1 ∪ Δ2)
      ESEHole : ∀{ Γ u } →
                Γ ⊢ ⦇⦈[ u ] ⇒ ⦇⦈ ~> ⦇⦈[ u , id Γ ] ⊣  ⟦ u ::[ Γ ] ⦇⦈ ⟧
      ESNEHole : ∀{ Γ e t d u Δ } →
                 Γ ⊢ e ⇒ t ~> d ⊣ Δ →
                 Γ ⊢ ⦇ e ⦈[ u ] ⇒ ⦇⦈ ~> ⦇ d ⦈[ u , id Γ ] ⊣ (Δ ,, u ::[ Γ ] ⦇⦈)
      ESAsc1 : ∀ {Γ e t d t' Δ} →
                 Γ ⊢ e ⇐ t ~> d :: t' ⊣ Δ →
                 (t == t' → ⊥) →
                 Γ ⊢ (e ·: t) ⇒ t ~> (< t > d) ⊣ Δ
      ESAsc2 : ∀{Γ e t d t' Δ } →
               Γ ⊢ e ⇐ t ~> d :: t' ⊣ Δ →
               Γ ⊢ (e ·: t) ⇒ t ~> d ⊣ Δ

    data _⊢_⇐_~>_::_⊣_ : (Γ : tctx) (e : hexp) (t : htyp) (d : dhexp) (t' : htyp)(Δ : hctx) → Set where
      EALam : ∀{Γ x t1 t2 e d t2' Δ } →
              (Γ ,, (x , t1)) ⊢ e ⇐ t2 ~> d :: t2' ⊣ Δ →
              Γ ⊢ ·λ x e ⇐ t1 ==> t2 ~> ·λ x [ t1 ] d :: t1 ==> t2' ⊣ Δ
      EASubsume : ∀{e u e' Γ t' d Δ t} →
                  (e == ⦇⦈[ u ] → ⊥) →
                  (e == ⦇ e' ⦈[ u ] → ⊥) →
                  Γ ⊢ e ⇒ t' ~> d ⊣ Δ →
                  t ~ t' →
                  Γ ⊢ e ⇐ t ~> d :: t' ⊣ Δ
      EAEHole : ∀{ Γ u t  } →
                Γ ⊢ ⦇⦈[ u ] ⇐ t ~> ⦇⦈[ u , id Γ ] :: t ⊣ ⟦ u ::[ Γ ] t ⟧
      EANEHole : ∀{ Γ e u t d t' Δ  } →
                 Γ ⊢ e ⇒ t' ~> d ⊣ Δ →
                 t ~ t' →
                 Γ ⊢ ⦇ e ⦈[ u ] ⇐ t ~> ⦇ d ⦈[ u , id Γ ] :: t ⊣ (Δ ,, u ::[ Γ ] t)

  -- type assignment
  data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (d : dhexp) (t : htyp) → Set where
    TAConst : ∀{Δ Γ} → Δ , Γ ⊢ c :: b
    TAVar : ∀{Δ Γ x t} → Δ , (Γ ,, (x , t)) ⊢ X x :: t
    TALam : ∀{ Δ Γ x t1 d t2} →
            Δ , (Γ ,, (x , t1)) ⊢ d :: t2 →
            Δ , Γ ⊢ ·λ x [ t1 ] d :: (t1 ==> t2)
    TAAp : ∀{ Δ Γ d1 d2 t1 t2 t} →
           Δ , Γ ⊢ d1 :: t1 →
           t1 ▸arr (t2 ==> t) →
           Δ , Γ ⊢ d2 :: t2 →
           Δ , Γ ⊢ d1 ∘ d2 :: t
    -- TAEHole : ∀{ Δ Γ σ u Γ' } → -- todo: overloaded form in the paper here
    -- TANEHole : ∀ { Δ Γ e t' Γ' u σ t }
    TACast : ∀{ Δ Γ d t t'} →
           Δ , Γ ⊢ d :: t' →
           t ~ t' →
           Δ , Γ ⊢ < t > d :: t

  -- todo: substition goes here

  -- value
  data _val : (d : dhexp) → Set where
    VConst : c val
    VLam   : ∀{x t d} → (·λ x [ t ] d) val

  mutual
    -- indeterminate
    data _indet : (d : dhexp) → Set where
      IEHole : ∀{u σ} → ⦇⦈[ u , σ ] indet
      INEHole : ∀{d u σ} → d final → ⦇ d ⦈[ u , σ ] indet
      IAp : ∀{d1 d2} → d1 indet → d2 final → (d1 ∘ d2) indet
      ICast : ∀{d t} → d indet → (< t > d) indet

    -- final
    data _final : (d : dhexp) → Set where
      FVal : ∀{d} → d val → d final
      FIndet : ∀{d} → d indet → d final

  -- error
  data _err[_] : (d : dhexp) → (Δ : hctx) → Set where
    -- ERNEHole
    -- ERCastError
    -- ERLam
    -- ERAp1
    -- ERAp2
    -- ERCast

  -- small step semantics
  data _↦_ : (d d' : dhexp) → Set where
    STHole : ∀{ d d' u σ } →
             d ↦ d' →
             ⦇ d ⦈[ u , σ ] ↦ ⦇ d' ⦈[ u , σ ]
    -- STCast
    STAp1 : ∀{ d1 d2 d1' } →
            d1 ↦ d1' →
            (d1 ∘ d2) ↦ (d1' ∘ d2)
    STAp2 : ∀{ d1 d2 d2' } →
            d1 final →
            d2 ↦ d2' →
            (d1 ∘ d2) ↦ (d1 ∘ d2')
    STApβ : ∀{ d1 d2 t x } →
            d2 final →
            ((·λ x [ t ] d1) ∘ d2) ↦ ([ ⟦ x , c ⟧ ] d2)
