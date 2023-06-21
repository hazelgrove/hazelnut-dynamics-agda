open import Nat
open import Prelude
open import contexts

module core where
  -- types
  data htyp : Set where
    b     : htyp
    A     : Nat → htyp
    ⦇-⦈    : htyp
    _==>_ : htyp → htyp → htyp
    ·∀    : Nat → htyp → htyp

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  -- external expressions
  data hexp : Set where
    c       : hexp
    _·:_    : hexp → htyp → hexp
    X       : Nat → hexp
    ·λ      : Nat → hexp → hexp
    ·λ_[_]_ : Nat → htyp → hexp → hexp
    ·Λ      : Nat → hexp → hexp
    ⦇-⦈[_]   : Nat → hexp
    ⦇⌜_⌟⦈[_]  : hexp → Nat → hexp
    _∘_     : hexp → hexp → hexp
    _<_>    : hexp → htyp → hexp

  -- the type of type contexts, i.e. Γs in the judegments below
  tctx : Set
  tctx = htyp ctx

  mutual
    -- identity substitution, substitition environments
    data env : Set where
      Id : (Γ : tctx) → env
      Subst : (d : ihexp) → (y : Nat) → env → env

    -- internal expressions
    data ihexp : Set where
      c         : ihexp
      X         : Nat → ihexp
      ·λ_[_]_   : Nat → htyp → ihexp → ihexp
      ·Λ        : Nat → ihexp → ihexp
      ⦇-⦈⟨_⟩     : (Nat × env) → ihexp
      ⦇⌜_⌟⦈⟨_⟩    : ihexp → (Nat × env) → ihexp
      _∘_       : ihexp → ihexp → ihexp
      _<_>      : ihexp → htyp → ihexp
      _⟨_⇒_⟩    : ihexp → htyp → htyp → ihexp
      _⟨_⇒⦇-⦈⇏_⟩ : ihexp → htyp → htyp → ihexp

  -- convenient notation for chaining together two agreeable casts
  _⟨_⇒_⇒_⟩ : ihexp → htyp → htyp → htyp → ihexp
  d ⟨ t1 ⇒ t2 ⇒ t3 ⟩ = d ⟨ t1 ⇒ t2 ⟩ ⟨ t2 ⇒ t3 ⟩

  -- definition of type consistency context, represented as a list of pairs of naturals indexing type variables
  module ~ctx where

    data ~ctx : Set where
      ~∅     : ~ctx
      _,_~_ : ~ctx → Nat → Nat → ~ctx

    data _∋_~_ : (Γ : ~ctx) (a b : Nat) → Set where
      H : ∀{Γ a b} → (Γ , a ~ b) ∋ a ~ b
      T : ∀{Γ a b a' b'} → Γ ∋ a ~ b → (Γ , a' ~ b') ∋ a ~ b

  open ~ctx

  -- type consistency in a type consistency context
  data _⊢_~_ : ~ctx → htyp → htyp → Set where 
    TCVar  : ∀{Γ a b} → Γ ∋ a ~ b → Γ ⊢ (A a) ~ (A b)
    TCBase : ∀{Γ} → Γ ⊢ b ~ b
    TCHole1 : ∀{Γ τ} → Γ ⊢ τ ~ ⦇-⦈
    TCHole2 : ∀{Γ τ} → Γ ⊢ ⦇-⦈ ~ τ
    TCArr   : ∀{Γ τ1 τ2 τ1' τ2'} →
               Γ ⊢ τ1 ~ τ1' →
               Γ ⊢ τ2 ~ τ2' →
               Γ ⊢ τ1 ==> τ2 ~ τ1' ==> τ2'
    TCForall : ∀{Γ a b τ τ'} →
              (Γ , a ~ b) ⊢ τ ~ τ' →
              Γ ⊢ ·∀ a τ ~ ·∀ b τ'

  -- type consistency
  _~_ : (t1 t2 : htyp) → Set
  _~_ = \(t1 t2 : htyp) → ~∅ ⊢ t1 ~ t2

  -- type inconsistency
  _~̸_ : (τ1 τ2 : htyp) → Set
  τ1 ~̸  τ2 = ¬(τ1 ~ τ2)

  --- matching for arrows
  data _▸arr_ : htyp → htyp → Set where
    MAHole : ⦇-⦈ ▸arr ⦇-⦈ ==> ⦇-⦈
    MAArr  : {τ1 τ2 : htyp} → τ1 ==> τ2 ▸arr τ1 ==> τ2

  --- matching for foralls
  data _▸forall_ : htyp → htyp → Set where
    -- the 0 in the line below is a placeholder variable;
    -- I'm not sure if it's safe to use here TODO
    MFHole : ⦇-⦈ ▸forall (·∀ 0 ⦇-⦈)
    MFForall  : ∀{a τ} → (·∀ a τ) ▸forall (·∀ a τ)

  -- the type of hole contexts, i.e. Δs in the judgements
  hctx : Set
  hctx = (htyp ctx × htyp) ctx

  -- notation for a triple to match the CMTT syntax
  _::_[_] : Nat → htyp → tctx → (Nat × (tctx × htyp))
  u :: τ [ Γ ] = u , (Γ , τ)

  -- the hole name u does not appear in the term e
  data hole-name-new : (e : hexp) (u : Nat) → Set where
    HNConst : ∀{u} → hole-name-new c u
    HNAsc : ∀{e τ u} →
            hole-name-new e u →
            hole-name-new (e ·: τ) u
    HNVar : ∀{x u} → hole-name-new (X x) u
    HNLam1 : ∀{x e u} →
             hole-name-new e u →
             hole-name-new (·λ x e) u
    HNLam2 : ∀{x e u τ} →
             hole-name-new e u →
             hole-name-new (·λ x [ τ ] e) u
    HNTLam : ∀{a e u} → 
             hole-name-new e u → 
             hole-name-new (·Λ a e) u
    HNHole : ∀{u u'} →
             u' ≠ u →
             hole-name-new (⦇-⦈[ u' ]) u
    HNNEHole : ∀{u u' e} →
               u' ≠ u →
               hole-name-new e u →
               hole-name-new (⦇⌜ e ⌟⦈[ u' ]) u
    HNAp : ∀{u e1 e2} →
           hole-name-new e1 u →
           hole-name-new e2 u →
           hole-name-new (e1 ∘ e2) u
    HNTAp : ∀{u e τ} →
        hole-name-new e u → 
        hole-name-new (e < τ >) u

  -- two terms that do not share any hole names
  data holes-disjoint : (e1 : hexp) → (e2 : hexp) → Set where
    HDConst : ∀{e} → holes-disjoint c e
    HDAsc : ∀{e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (e1 ·: τ) e2
    HDVar : ∀{x e} → holes-disjoint (X x) e
    HDLam1 : ∀{x e1 e2} → holes-disjoint e1 e2 → holes-disjoint (·λ x e1) e2
    HDLam2 : ∀{x e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (·λ x [ τ ] e1) e2
    HDTLam : ∀{a e1 e2} → holes-disjoint e1 e2 → holes-disjoint (·Λ a e1) e2
    HDHole : ∀{u e2} → hole-name-new e2 u → holes-disjoint (⦇-⦈[ u ]) e2
    HDNEHole : ∀{u e1 e2} → hole-name-new e2 u → holes-disjoint e1 e2 → holes-disjoint (⦇⌜ e1 ⌟⦈[ u ]) e2
    HDAp :  ∀{e1 e2 e3} → holes-disjoint e1 e3 → holes-disjoint e2 e3 → holes-disjoint (e1 ∘ e2) e3
    HDTAp : ∀{e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (e1 < τ >) e2

  -- definition of type context, represented as a list of naturals indexing type variables
  module typctx where

    data typctx : Set where
      ~∅     : typctx
      _,_Type : typctx → Nat → typctx

    data _∋_Type : (Θ : typctx) (a : Nat) → Set where
      H : ∀{Θ a} → (Θ , a Type) ∋ a Type
      T : ∀{Θ a a'} → Θ ∋ a Type → (Θ , a' Type) ∋ a Type

  open typctx

  -- substitution in types
  Typ[_/_]_ : htyp → Nat → htyp → htyp 
  Typ[ τ / a ] b = b
  Typ[ τ / a ] A a'
    with natEQ a a'
  Typ[ τ / a ] A a' | Inl refl = τ
  Typ[ τ / a ] A a' | Inr neq = A a'
  Typ[ τ / a ] ⦇-⦈ = ⦇-⦈
  Typ[ τ / a ] (τ1 ==> τ2) = ((Typ[ τ / a ] τ1) ==> (Typ[ τ / a ] τ2))
  Typ[ τ / a ] (·∀ a' τ')
    with natEQ a a'
  Typ[ τ / a ] (·∀ a' τ') | Inl refl = ·∀ a' τ'
  Typ[ τ / a ] (·∀ a' τ') | Inr neq = ·∀ a' (Typ[ τ / a ] τ')

  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _,_⊢_=>_ : (Γ : tctx) (Θ : typctx) (e : hexp) (τ : htyp) → Set where
      SConst  : {Γ : tctx} {Θ : typctx} → Γ , Θ ⊢ c => b
      SAsc    : {Γ : tctx} {Θ : typctx} {e : hexp} {τ : htyp} →
                 Γ , Θ ⊢ e <= τ →
                 Γ , Θ ⊢ (e ·: τ) => τ
      SVar    : {Γ : tctx} {Θ : typctx} {τ : htyp} {x : Nat} →
                 (x , τ) ∈ Γ →
                 Γ , Θ ⊢ X x => τ
      SAp     : {Γ : tctx} {Θ : typctx} {e1 e2 : hexp} {τ τ1 τ2 : htyp} →
                 holes-disjoint e1 e2 →
                 Γ , Θ ⊢ e1 => τ1 →
                 τ1 ▸arr τ2 ==> τ →
                 Γ , Θ ⊢ e2 <= τ2 →
                 Γ , Θ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Γ : tctx} {Θ : typctx} {u : Nat} → Γ , Θ ⊢ ⦇-⦈[ u ] => ⦇-⦈
      SNEHole : {Γ : tctx} {Θ : typctx} {e : hexp} {τ : htyp} {u : Nat} →
                 hole-name-new e u →
                 Γ , Θ ⊢ e => τ →
                 Γ , Θ ⊢ ⦇⌜ e ⌟⦈[ u ] => ⦇-⦈
      SLam    : {Γ : tctx} {Θ : typctx} {e : hexp} {τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 (Γ ,, (x , τ1)) , Θ ⊢ e => τ2 →
                 Γ , Θ ⊢ ·λ x [ τ1 ] e => τ1 ==> τ2
      STLam   : {Γ : tctx} {Θ : typctx} {e : hexp} {τ : htyp} {a : Nat} → 
                Γ , (Θ , a Type) ⊢ e => τ → 
                Γ , Θ ⊢ (·Λ a e) => (·∀ a τ)
      STAp    : {Γ : tctx} {Θ : typctx} {e : hexp} {τ1 τ2 τ3 : htyp} {a : Nat} → 
                Γ , Θ ⊢ e => τ2 →
                τ2 ▸forall (·∀ a τ3) →
                Γ , Θ ⊢ (e < τ1 >) => (Typ[ τ1 / a ] τ3)

    -- analysis
    data _,_⊢_<=_ : (Γ : htyp ctx) (Θ : typctx) (e : hexp) (τ : htyp) → Set where
      ASubsume : {Γ : tctx} {Θ : typctx} {e : hexp} {τ τ' : htyp} →
                 Γ , Θ ⊢ e => τ' →
                 τ ~ τ' →
                 Γ , Θ ⊢ e <= τ
      ALam : {Γ : tctx} {Θ : typctx} {e : hexp} {τ τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 τ ▸arr τ1 ==> τ2 →
                 (Γ ,, (x , τ1)) , Θ ⊢ e <= τ2 →
                 Γ , Θ ⊢ (·λ x e) <= τ
      ATLam : {Γ : tctx} {Θ : typctx} {e : hexp} {τ1 τ2 : htyp} {a : Nat} → 
                τ1 ▸forall (·∀ a τ2) → 
                Γ , (Θ , a Type) ⊢ e <= τ2 → 
                Γ , Θ ⊢ (·Λ a e) <= τ1

  -- those types without holes
  data _tcomplete : htyp → Set where
    TCBase : b tcomplete
    TCVar : ∀{a} → (A a) tcomplete
    TCArr : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ==> τ2) tcomplete
    TCForall : ∀{a e} → e tcomplete → (·∀ a e) tcomplete 

  -- those external expressions without holes
  data _ecomplete : hexp → Set where
    ECConst : c ecomplete
    ECAsc : ∀{τ e} → τ tcomplete → e ecomplete → (e ·: τ) ecomplete
    ECVar : ∀{x} → (X x) ecomplete
    ECLam1 : ∀{x e} → e ecomplete → (·λ x e) ecomplete
    ECLam2 : ∀{x e τ} → e ecomplete → τ tcomplete → (·λ x [ τ ] e) ecomplete
    ECTLam : ∀{a e} → e ecomplete → (·Λ a e) ecomplete
    ECAp : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECTAp : ∀{τ e} → τ tcomplete → e ecomplete → (e < τ >) ecomplete

  -- those internal expressions without holes
  data _dcomplete : ihexp → Set where
    DCVar : ∀{x} → (X x) dcomplete
    DCConst : c dcomplete
    DCLam : ∀{x τ d} → d dcomplete → τ tcomplete → (·λ x [ τ ] d) dcomplete
    DCTLam : ∀{a d} → d dcomplete → (·Λ a d) dcomplete
    DCAp : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → (d1 ∘ d2) dcomplete
    DCTAp : ∀{τ d} → τ tcomplete → d dcomplete → (d < τ >) dcomplete
    DCCast : ∀{d τ1 τ2} → d dcomplete → τ1 tcomplete → τ2 tcomplete → (d ⟨ τ1 ⇒ τ2 ⟩) dcomplete

  -- contexts that only produce complete types
  _gcomplete : tctx → Set
  Γ gcomplete = (x : Nat) (τ : htyp) → (x , τ) ∈ Γ → τ tcomplete

  -- those internal expressions where every cast is the identity cast and
  -- there are no failed casts
  data cast-id : ihexp → Set where
    CIConst  : cast-id c
    CIVar    : ∀{x} → cast-id (X x)
    CILam    : ∀{x τ d} → cast-id d → cast-id (·λ x [ τ ] d)
    CITLam   : ∀{a d} → cast-id d → cast-id (·Λ a d)
    CIHole   : ∀{u} → cast-id (⦇-⦈⟨ u ⟩)
    CINEHole : ∀{d u} → cast-id d → cast-id (⦇⌜ d ⌟⦈⟨ u ⟩)
    CIAp     : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ∘ d2)
    CITap    : ∀{τ d} → cast-id d → cast-id (d < τ >)
    CICast   : ∀{d τ} → cast-id d → cast-id (d ⟨ τ ⇒ τ ⟩)

  -- expansion
  mutual
    -- synthesis
    data _,_⊢_⇒_~>_⊣_ : (Γ : tctx) (Θ : typctx) (e : hexp) (τ : htyp) (d : ihexp) (Δ : hctx) → Set where
      ESConst : ∀{Γ Θ} → Γ , Θ ⊢ c ⇒ b ~> c ⊣ ∅
      ESVar   : ∀{Γ Θ x τ} → (x , τ) ∈ Γ →
                         Γ , Θ ⊢ X x ⇒ τ ~> X x ⊣ ∅
      ESLam   : ∀{Γ Θ x τ1 τ2 e d Δ} →
                     (x # Γ) →
                     (Γ ,, (x , τ1)) , Θ ⊢ e ⇒ τ2 ~> d ⊣ Δ →
                      Γ , Θ ⊢ ·λ x [ τ1 ] e ⇒ (τ1 ==> τ2) ~> ·λ x [ τ1 ] d ⊣ Δ
      ESAp : ∀{Γ Θ e1 τ τ1 τ1' τ2 τ2' d1 Δ1 e2 d2 Δ2} →
              holes-disjoint e1 e2 →
              Δ1 ## Δ2 →
              Γ , Θ ⊢ e1 => τ1 →
              τ1 ▸arr τ2 ==> τ →
              Γ , Θ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' ⊣ Δ1 →
              Γ , Θ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
              Γ , Θ ⊢ e1 ∘ e2 ⇒ τ ~> (d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩) ⊣ (Δ1 ∪ Δ2)
      ESEHole : ∀{Γ Θ u} →
                Γ , Θ ⊢ ⦇-⦈[ u ] ⇒ ⦇-⦈ ~> ⦇-⦈⟨ u , Id Γ ⟩ ⊣  ■ (u :: ⦇-⦈ [ Γ ])
      ESNEHole : ∀{Γ Θ e τ d u Δ} →
                 Δ ## (■ (u , Γ , ⦇-⦈)) →
                 Γ , Θ ⊢ e ⇒ τ ~> d ⊣ Δ →
                 Γ , Θ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇒ ⦇-⦈ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ ⊣ (Δ ,, u :: ⦇-⦈ [ Γ ])
      ESAsc : ∀ {Γ Θ e τ d τ' Δ} →
                 Γ , Θ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                 Γ , Θ ⊢ (e ·: τ) ⇒ τ ~> d ⟨ τ' ⇒ τ ⟩ ⊣ Δ

    -- analysis
    data _,_⊢_⇐_~>_::_⊣_ : (Γ : tctx) (Θ : typctx) (e : hexp) (τ : htyp) (d : ihexp) (τ' : htyp) (Δ : hctx) → Set where
      EALam : ∀{Γ Θ x τ τ1 τ2 e d τ2' Δ } →
              (x # Γ) →
              τ ▸arr τ1 ==> τ2 →
              (Γ ,, (x , τ1)) , Θ ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
              Γ , Θ ⊢ ·λ x e ⇐ τ ~> ·λ x [ τ1 ] d :: τ1 ==> τ2' ⊣ Δ
      EASubsume : ∀{e Γ Θ τ' d Δ τ} →
                  ((u : Nat) → e ≠ ⦇-⦈[ u ]) →
                  ((e' : hexp) (u : Nat) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
                  Γ , Θ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  τ ~ τ' →
                  Γ , Θ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
      EAEHole : ∀{Γ Θ u τ} →
                Γ , Θ ⊢ ⦇-⦈[ u ] ⇐ τ ~> ⦇-⦈⟨ u , Id Γ  ⟩ :: τ ⊣ ■ (u :: τ [ Γ ])
      EANEHole : ∀{Γ Θ e u τ d τ' Δ} →
                 Δ ## (■ (u , Γ , τ)) →
                 Γ , Θ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                 Γ , Θ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇐ τ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ :: τ ⊣ (Δ ,, u :: τ [ Γ ])

  -- ground types
  data _ground : (τ : htyp) → Set where
    GBase : b ground
    GHole : ⦇-⦈ ==> ⦇-⦈ ground

  mutual
    -- substitution typing
    data _,_⊢_:s:_ : hctx → tctx → env → tctx → Set where
      STAId : ∀{Γ Γ' Δ} →
                  ((x : Nat) (τ : htyp) → (x , τ) ∈ Γ' → (x , τ) ∈ Γ) →
                  Δ , Γ ⊢ Id Γ' :s: Γ'
      STASubst : ∀{Γ Δ σ y Γ' d τ } →
               Δ , Γ ,, (y , τ) ⊢ σ :s: Γ' →
               Δ , Γ ⊢ d :: τ →
               Δ , Γ ⊢ Subst d y σ :s: Γ'

    -- type assignment
    data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (d : ihexp) (τ : htyp) → Set where
      TAConst : ∀{Δ Γ} → Δ , Γ ⊢ c :: b
      TAVar : ∀{Δ Γ x τ} → (x , τ) ∈ Γ → Δ , Γ ⊢ X x :: τ
      TALam : ∀{ Δ Γ x τ1 d τ2} →
              x # Γ →
              Δ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
              Δ , Γ ⊢ ·λ x [ τ1 ] d :: (τ1 ==> τ2)
      TAAp : ∀{ Δ Γ d1 d2 τ1 τ} →
             Δ , Γ ⊢ d1 :: τ1 ==> τ →
             Δ , Γ ⊢ d2 :: τ1 →
             Δ , Γ ⊢ d1 ∘ d2 :: τ
      TAEHole : ∀{ Δ Γ σ u Γ' τ} →
                (u , (Γ' , τ)) ∈ Δ →
                Δ , Γ ⊢ σ :s: Γ' →
                Δ , Γ ⊢ ⦇-⦈⟨ u , σ ⟩ :: τ
      TANEHole : ∀ { Δ Γ d τ' Γ' u σ τ } →
                 (u , (Γ' , τ)) ∈ Δ →
                 Δ , Γ ⊢ d :: τ' →
                 Δ , Γ ⊢ σ :s: Γ' →
                 Δ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ u , σ ⟩ :: τ
      TACast : ∀{ Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 →
             τ1 ~ τ2 →
             Δ , Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
      TAFailedCast : ∀{Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 →
             τ1 ground →
             τ2 ground →
             τ1 ≠ τ2 →
             Δ , Γ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ :: τ2

  -- substitution
  [_/_]_ : ihexp → Nat → ihexp → ihexp
  [ d / y ] c = c
  [ d / y ] X x
    with natEQ x y
  [ d / y ] X .y | Inl refl = d
  [ d / y ] X x  | Inr neq = X x
  [ d / y ] (·λ x [ x₁ ] d')
    with natEQ x y
  [ d / y ] (·λ .y [ τ ] d') | Inl refl = ·λ y [ τ ] d'
  [ d / y ] (·λ x [ τ ] d')  | Inr x₁ = ·λ x [ τ ] ( [ d / y ] d')
  [ d / y ] ⦇-⦈⟨ u , σ ⟩ = ⦇-⦈⟨ u , Subst d y σ ⟩
  [ d / y ] ⦇⌜ d' ⌟⦈⟨ u , σ  ⟩ =  ⦇⌜ [ d / y ] d' ⌟⦈⟨ u , Subst d y σ ⟩
  [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
  [ d / y ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / y ] (d' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩

  -- applying an environment to an expression
  apply-env : env → ihexp → ihexp
  apply-env (Id Γ) d = d
  apply-env (Subst d y σ) d' = [ d / y ] ( apply-env σ d')

  -- values
  data _val : (d : ihexp) → Set where
    VConst : c val
    VLam   : ∀{x τ d} → (·λ x [ τ ] d) val

  -- boxed values
  data _boxedval : (d : ihexp) → Set where
    BVVal : ∀{d} → d val → d boxedval
    BVArrCast : ∀{ d τ1 τ2 τ3 τ4 } →
                τ1 ==> τ2 ≠ τ3 ==> τ4 →
                d boxedval →
                d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ boxedval
    BVHoleCast : ∀{ τ d } → τ ground → d boxedval → d ⟨ τ ⇒ ⦇-⦈ ⟩ boxedval

  mutual
    -- indeterminate forms
    data _indet : (d : ihexp) → Set where
      IEHole : ∀{u σ} → ⦇-⦈⟨ u , σ ⟩ indet
      INEHole : ∀{d u σ} → d final → ⦇⌜ d ⌟⦈⟨ u , σ ⟩ indet
      IAp : ∀{d1 d2} → ((τ1 τ2 τ3 τ4 : htyp) (d1' : ihexp) →
                       d1 ≠ (d1' ⟨(τ1 ==> τ2) ⇒ (τ3 ==> τ4)⟩)) →
                       d1 indet →
                       d2 final →
                       (d1 ∘ d2) indet
      ICastArr : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ==> τ2 ≠ τ3 ==> τ4 →
                 d indet →
                 d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ indet
      ICastGroundHole : ∀{ τ d } →
                        τ ground →
                        d indet →
                        d ⟨ τ ⇒  ⦇-⦈ ⟩ indet
      ICastHoleGround : ∀ { d τ } →
                        ((d' : ihexp) (τ' : htyp) → d ≠ (d' ⟨ τ' ⇒ ⦇-⦈ ⟩)) →
                        d indet →
                        τ ground →
                        d ⟨ ⦇-⦈ ⇒ τ ⟩ indet
      IFailedCast : ∀{ d τ1 τ2 } →
                    d final →
                    τ1 ground →
                    τ2 ground →
                    τ1 ≠ τ2 →
                    d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ indet

    -- final expressions
    data _final : (d : ihexp) → Set where
      FBoxedVal : ∀{d} → d boxedval → d final
      FIndet    : ∀{d} → d indet    → d final


  -- contextual dynamics

  -- evaluation contexts
  data ectx : Set where
    ⊙ : ectx
    _∘₁_ : ectx → ihexp → ectx
    _∘₂_ : ihexp → ectx → ectx
    ⦇⌜_⌟⦈⟨_⟩ : ectx → (Nat × env ) → ectx
    _⟨_⇒_⟩ : ectx → htyp → htyp → ectx
    _⟨_⇒⦇-⦈⇏_⟩ : ectx → htyp → htyp → ectx

  -- note: this judgement is redundant: in the absence of the premises in
  -- the red brackets, all syntactically well formed ectxs are valid. with
  -- finality premises, that's not true, and that would propagate through
  -- additions to the calculus. so we leave it here for clarity but note
  -- that, as written, in any use case its either trival to prove or
  -- provides no additional information

   --ε is an evaluation context
  data _evalctx : (ε : ectx) → Set where
    ECDot : ⊙ evalctx
    ECAp1 : ∀{d ε} →
            ε evalctx →
            (ε ∘₁ d) evalctx
    ECAp2 : ∀{d ε} →
            -- d final → -- red brackets
            ε evalctx →
            (d ∘₂ ε) evalctx
    ECNEHole : ∀{ε u σ} →
               ε evalctx →
               ⦇⌜ ε ⌟⦈⟨ u , σ ⟩ evalctx
    ECCast : ∀{ ε τ1 τ2} →
             ε evalctx →
             (ε ⟨ τ1 ⇒ τ2 ⟩) evalctx
    ECFailedCast : ∀{ ε τ1 τ2 } →
                   ε evalctx →
                   ε ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ evalctx

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
    FHNEHole : ∀{ d d' ε u σ} →
              d == ε ⟦ d' ⟧ →
              ⦇⌜ d ⌟⦈⟨ (u , σ ) ⟩ ==  ⦇⌜ ε ⌟⦈⟨ (u , σ ) ⟩ ⟦ d' ⟧
    FHCast : ∀{ d d' ε τ1 τ2 } →
            d == ε ⟦ d' ⟧ →
            d ⟨ τ1 ⇒ τ2 ⟩ == ε ⟨ τ1 ⇒ τ2 ⟩ ⟦ d' ⟧
    FHFailedCast : ∀{ d d' ε τ1 τ2} →
            d == ε ⟦ d' ⟧ →
            (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) == (ε ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⟦ d' ⟧

  -- matched ground types
  data _▸gnd_ : htyp → htyp → Set where
    MGArr : ∀{τ1 τ2} →
            (τ1 ==> τ2) ≠ (⦇-⦈ ==> ⦇-⦈) →
            (τ1 ==> τ2) ▸gnd (⦇-⦈ ==> ⦇-⦈)

  -- instruction transition judgement
  data _→>_ : (d d' : ihexp) → Set where
    ITLam : ∀{ x τ d1 d2 } →
            -- d2 final → -- red brackets
            ((·λ x [ τ ] d1) ∘ d2) →> ([ d2 / x ] d1)
    ITCastID : ∀{d τ } →
               -- d final → -- red brackets
               (d ⟨ τ ⇒ τ ⟩) →> d
    ITCastSucceed : ∀{d τ } →
                    -- d final → -- red brackets
                    τ ground →
                    (d ⟨ τ ⇒ ⦇-⦈ ⇒ τ ⟩) →> d
    ITCastFail : ∀{ d τ1 τ2} →
                 -- d final → -- red brackets
                 τ1 ground →
                 τ2 ground →
                 τ1 ≠ τ2 →
                 (d ⟨ τ1 ⇒ ⦇-⦈ ⇒ τ2 ⟩) →> (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
    ITApCast : ∀{d1 d2 τ1 τ2 τ1' τ2' } →
               -- d1 final → -- red brackets
               -- d2 final → -- red brackets
               ((d1 ⟨ (τ1 ==> τ2) ⇒ (τ1' ==> τ2')⟩) ∘ d2) →> ((d1 ∘ (d2 ⟨ τ1' ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ2' ⟩)
    ITGround : ∀{ d τ τ'} →
               -- d final → -- red brackets
               τ ▸gnd τ' →
               (d ⟨ τ ⇒ ⦇-⦈ ⟩) →> (d ⟨ τ ⇒ τ' ⇒ ⦇-⦈ ⟩)
    ITExpand : ∀{d τ τ' } →
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

  -- freshness
  mutual
    -- ... with respect to a hole context
    data envfresh : Nat → env → Set where
      EFId : ∀{x Γ} → x # Γ → envfresh x (Id Γ)
      EFSubst : ∀{x d σ y} → fresh x d
                           → envfresh x σ
                           → x ≠ y
                           → envfresh x (Subst d y σ)

    -- ... for inernal expressions
    data fresh : Nat → ihexp → Set where
      FConst : ∀{x} → fresh x c
      FVar   : ∀{x y} → x ≠ y → fresh x (X y)
      FLam   : ∀{x y τ d} → x ≠ y → fresh x d → fresh x (·λ y [ τ ] d)
      FHole  : ∀{x u σ} → envfresh x σ → fresh x (⦇-⦈⟨ u , σ ⟩)
      FNEHole : ∀{x d u σ} → envfresh x σ → fresh x d → fresh x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      FAp     : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x (d1 ∘ d2)
      FCast   : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒ τ2 ⟩)
      FFailedCast : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  -- ... for external expressions
  data freshh : Nat → hexp → Set where
    FRHConst : ∀{x} → freshh x c
    FRHAsc   : ∀{x e τ} → freshh x e → freshh x (e ·: τ)
    FRHVar   : ∀{x y} → x ≠ y → freshh x (X y)
    FRHLam1  : ∀{x y e} → x ≠ y → freshh x e → freshh x (·λ y e)
    FRHLam2  : ∀{x τ e y} → x ≠ y → freshh x e → freshh x (·λ y [ τ ] e)
    FRHEHole : ∀{x u} → freshh x (⦇-⦈[ u ])
    FRHNEHole : ∀{x u e} → freshh x e → freshh x (⦇⌜ e ⌟⦈[ u ])
    FRHAp : ∀{x e1 e2} → freshh x e1 → freshh x e2 → freshh x (e1 ∘ e2)

  -- x is not used in a binding site in d
  mutual
    data unbound-in-σ : Nat → env → Set where
      UBσId : ∀{x Γ} → unbound-in-σ x (Id Γ)
      UBσSubst : ∀{x d y σ} → unbound-in x d
                            → unbound-in-σ x σ
                            → x ≠ y
                            → unbound-in-σ x (Subst d y σ)

    data unbound-in : (x : Nat) (d : ihexp) → Set where
      UBConst : ∀{x} → unbound-in x c
      UBVar : ∀{x y} → unbound-in x (X y)
      UBLam2 : ∀{x d y τ} → x ≠ y
                           → unbound-in x d
                           → unbound-in x (·λ_[_]_ y τ d)
      UBHole : ∀{x u σ} → unbound-in-σ x σ
                         → unbound-in x (⦇-⦈⟨ u , σ ⟩)
      UBNEHole : ∀{x u σ d }
                  → unbound-in-σ x σ
                  → unbound-in x d
                  → unbound-in x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      UBAp : ∀{ x d1 d2 } →
            unbound-in x d1 →
            unbound-in x d2 →
            unbound-in x (d1 ∘ d2)
      UBCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒ τ2 ⟩)
      UBFailedCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)


  mutual
    data binders-disjoint-σ : env → ihexp → Set where
      BDσId : ∀{Γ d} → binders-disjoint-σ (Id Γ) d
      BDσSubst : ∀{d1 d2 y σ} → binders-disjoint d1 d2
                              → binders-disjoint-σ σ d2
                              → binders-disjoint-σ (Subst d1 y σ) d2

    -- two terms that do not share any binders
    data binders-disjoint : (d1 : ihexp) → (d2 : ihexp) → Set where
      BDConst : ∀{d} → binders-disjoint c d
      BDVar : ∀{x d} → binders-disjoint (X x) d
      BDLam : ∀{x τ d1 d2} → binders-disjoint d1 d2
                            → unbound-in x d2
                            → binders-disjoint (·λ_[_]_ x τ d1) d2
      BDHole : ∀{u σ d2} → binders-disjoint-σ σ d2
                         → binders-disjoint (⦇-⦈⟨ u , σ ⟩) d2
      BDNEHole : ∀{u σ d1 d2} → binders-disjoint-σ σ d2
                              → binders-disjoint d1 d2
                              → binders-disjoint (⦇⌜ d1 ⌟⦈⟨ u , σ ⟩) d2
      BDAp :  ∀{d1 d2 d3} → binders-disjoint d1 d3
                          → binders-disjoint d2 d3
                          → binders-disjoint (d1 ∘ d2) d3
      BDCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒ τ2 ⟩) d2
      BDFailedCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) d2

  mutual
  -- each term has to be binders unique, and they have to be pairwise
  -- disjoint with the collection of bound vars
    data binders-unique-σ : env → Set where
      BUσId : ∀{Γ} → binders-unique-σ (Id Γ)
      BUσSubst : ∀{d y σ} → binders-unique d
                          → binders-unique-σ σ
                          → binders-disjoint-σ σ d
                          → binders-unique-σ (Subst d y σ)

    -- all the variable names in the term are unique
    data binders-unique : ihexp → Set where
      BUHole : binders-unique c
      BUVar : ∀{x} → binders-unique (X x)
      BULam : {x : Nat} {τ : htyp} {d : ihexp} → binders-unique d
                                                → unbound-in x d
                                                → binders-unique (·λ_[_]_ x τ d)
      BUEHole : ∀{u σ} → binders-unique-σ σ
                        → binders-unique (⦇-⦈⟨ u , σ ⟩)
      BUNEHole : ∀{u σ d} → binders-unique d
                           → binders-unique-σ σ
                           → binders-unique (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      BUAp : ∀{d1 d2} → binders-unique d1
                       → binders-unique d2
                       → binders-disjoint d1 d2
                       → binders-unique (d1 ∘ d2)
      BUCast : ∀{d τ1 τ2} → binders-unique d
                           → binders-unique (d ⟨ τ1 ⇒ τ2 ⟩)
      BUFailedCast : ∀{d τ1 τ2} → binders-unique d
                                 → binders-unique (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
