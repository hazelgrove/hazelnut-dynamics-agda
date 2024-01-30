
open import Nat
open import Prelude
open import contexts

module simple-core where

  -- types
  data htyp : Set where
    b     : htyp
    T     : Nat → htyp
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
    ⦇-⦈      : hexp
    ⦇⌜_⌟⦈   : hexp → hexp
    _∘_     : hexp → hexp → hexp
    _<_>    : hexp → htyp → hexp

  -- the type of type contexts, i.e. Γs in the judegments below
  tctx : Set
  tctx = htyp ctx

  -- the type of "type contexts" (name collision with above), containing 
  -- all type variables in scope, i.e. Θs in the judgements below
  typctx : Set
  typctx = ⊤ ctx

  data _,_⊢_=α_ : Nat ctx → Nat ctx → htyp → htyp → Set where 
    AlphaBase : ∀ {ΓL ΓR} → ΓL , ΓR ⊢ b =α b
    AlphaVarBound : ∀ {ΓL ΓR x y} → (x , y) ∈ ΓL → (y , x) ∈ ΓR → ΓL , ΓR ⊢ T x =α T y
    AlphaVarFree : ∀ {ΓL ΓR x} → (ΓL x == None) → (ΓR x == None) → ΓL , ΓR ⊢ T x =α T x
    AlphaHole : ∀ {ΓL ΓR} → ΓL , ΓR ⊢ ⦇-⦈ =α ⦇-⦈
    AlphaArr : ∀ {ΓL ΓR τ1 τ2 τ3 τ4} → ΓL , ΓR ⊢ τ1 =α τ3 → ΓL , ΓR ⊢ τ2 =α τ4 → ΓL , ΓR ⊢ τ1 ==> τ2 =α τ3 ==> τ4
    AlphaForall : ∀ {ΓL ΓR τ1 τ2 x y} → (■ (x , y) ∪ ΓL) ,  (■ (y , x) ∪ ΓR) ⊢ τ1 =α τ2 → ΓL , ΓR ⊢ ·∀ x τ1 =α ·∀ y τ2

  data _,_⊢_~_ : Nat ctx → Nat ctx → htyp → htyp → Set where 
    ConsistBase : ∀ {ΓL ΓR} → ΓL , ΓR ⊢ b ~ b
    ConsistVarBound : ∀ {ΓL ΓR x y} → (x , y) ∈ ΓL → (y , x) ∈ ΓR → ΓL , ΓR ⊢ T x ~ T y
    ConsistVarFree : ∀ {ΓL ΓR x} → (ΓL x == None) → (ΓR x == None) → ΓL , ΓR ⊢ T x ~ T x
    ConsistHole1 : ∀ {ΓL ΓR τ} → ΓL , ΓR ⊢ τ ~ ⦇-⦈
    ConsistHole2 : ∀ {ΓL ΓR τ} → ΓL , ΓR ⊢ ⦇-⦈ ~ τ
    ConsistArr : ∀ {ΓL ΓR τ1 τ2 τ3 τ4} → ΓL , ΓR ⊢ τ1 ~ τ3 → ΓL , ΓR ⊢ τ2 ~ τ4 → ΓL , ΓR ⊢ τ1 ==> τ2 ~ τ3 ==> τ4
    ConsistForall : ∀ {ΓL ΓR τ1 τ2 x y} → (■ (x , y) ∪ ΓL) ,  (■ (y , x) ∪ ΓR) ⊢ τ1 ~ τ2 → ΓL , ΓR ⊢ ·∀ x τ1 ~ ·∀ y τ2

  -- alpha equivalence of types
  _=α_ : htyp → htyp → Set 
  τ1 =α τ2 = ∅ , ∅ ⊢ τ1 =α τ2

  -- alpha inequivalence
  _=α̸_ : (t1 t2 : htyp) → Set
  _=α̸_ = \(t1 t2 : htyp) → ¬(t1 =α t2)

  -- (alpha) consistency of types
  _~_ : htyp → htyp → Set 
  τ1 ~ τ2 = ∅ , ∅ ⊢ τ1 ~ τ2

  -- type inconsistency
  _~̸_ : (t1 t2 : htyp) → Set
  _~̸_ = \(t1 t2 : htyp) → ¬(t1 ~ t2)

  --- matching for arrows
  data _▸arr_ : htyp → htyp → Set where
    MAHole : ⦇-⦈ ▸arr ⦇-⦈ ==> ⦇-⦈
    MAArr  : {τ1 τ2 : htyp} → τ1 ==> τ2 ▸arr τ1 ==> τ2

  --- matching for foralls
  data _▸forall_ : htyp → htyp → Set where
    MFHole : ∀{t} → ⦇-⦈ ▸forall (·∀ t ⦇-⦈)
    MFForall : ∀{t τ} → (·∀ t τ) ▸forall (·∀ t τ)

  -- internal expressions
  data ihexp : Set where
    c         : ihexp
    X         : Nat → ihexp
    ·λ_[_]_   : Nat → htyp → ihexp → ihexp
    ·Λ        : Nat → ihexp → ihexp
    ⦇-⦈⟨_⟩     : htyp → ihexp
    ⦇⌜_⌟⦈⟨_⟩    : ihexp → htyp → ihexp
    _∘_       : ihexp → ihexp → ihexp
    _<_>      : ihexp → htyp → ihexp
    _⟨_⇒_⟩    : ihexp → htyp → htyp → ihexp
    _⟨_⇒⦇-⦈⇏_⟩ : ihexp → htyp → htyp → ihexp

  -- convenient notation for chaining together two agreeable casts
  _⟨_⇒_⇒_⟩ : ihexp → htyp → htyp → htyp → ihexp
  d ⟨ t1 ⇒ t2 ⇒ t3 ⟩ = d ⟨ t1 ⇒ t2 ⟩ ⟨ t2 ⇒ t3 ⟩
  
  -- well-formedness of types
  data _⊢_wf : typctx → htyp → Set where
    WFVar : ∀{Θ a} → (a , <>) ∈ Θ → Θ ⊢ T a wf
    WFBase : ∀{Θ} → Θ ⊢ b wf
    WFHole : ∀{Θ} → Θ ⊢ ⦇-⦈ wf
    WFArr : ∀{Θ t1 t2} → Θ ⊢ t1 wf → Θ ⊢  t2 wf → Θ ⊢ t1 ==> t2 wf
    WFForall : ∀{Θ n t} → n # Θ → (Θ ,, (n , <>)) ⊢ t wf → Θ ⊢ ·∀ n t wf

  -- well-formedness of contexts
  data _⊢_tctxwf : typctx → tctx → Set where
    CCtx : ∀{Θ Γ} → (∀{x y} → (x , y) ∈ Γ → Θ ⊢ y wf) → Θ ⊢ Γ tctxwf

  -- substitution of types in types
  Typ[_/_]_ : htyp → Nat → htyp → htyp 
  Typ[ τ / a ] b = b
  Typ[ τ / a ] T a'
    with natEQ a a'
  Typ[ τ / a ] T a' | Inl refl = τ
  Typ[ τ / a ] T a' | Inr neq = T a'
  Typ[ τ / a ] ⦇-⦈ = ⦇-⦈
  Typ[ τ / a ] (τ1 ==> τ2) = ((Typ[ τ / a ] τ1) ==> (Typ[ τ / a ] τ2))
  Typ[ τ / a ] (·∀ t τ') with natEQ a t
  ...  | Inl refl = (·∀ t τ')
  ...  | Inr _ = ·∀ t (Typ[ τ / a ] τ')

  -- Type substitution binds tighter than consistency (20)
  infixl 21 Typ[_/_]_

  -- substitution of types in contexts
  Tctx[_/_]_ : htyp → Nat → tctx → tctx
  Tctx[ tau / t ] gamma = map (Typ[_/_]_ tau t) gamma
  
  -- substitution of types in terms 
  Ihexp[_/_]_ : htyp → Nat → ihexp → ihexp
  Ihexp[ τ / t ] c = c
  Ihexp[ τ / t ] (X x) = X x
  Ihexp[ τ / t ] (·λ x [ τx ] d) = ·λ x [ Typ[ τ / t ] τx ] (Ihexp[ τ / t ] d)
  Ihexp[ τ / t ] (·Λ t' d) with natEQ t t'
  ... | Inl refl = (·Λ t' d)
  ... | Inr neq = (·Λ t' (Ihexp[ τ / t ] d))
  Ihexp[ τ / t ] (⦇-⦈⟨ τ' ⟩) = ⦇-⦈⟨ Typ[ τ / t ] τ' ⟩
  Ihexp[ τ / t ] (⦇⌜ d ⌟⦈⟨  τ' ⟩) = ⦇⌜ (Ihexp[ τ / t ] d) ⌟⦈⟨ Typ[ τ / t ] τ' ⟩
  Ihexp[ τ / t ] (d1 ∘ d2) = ((Ihexp[ τ / t ] d1) ∘ (Ihexp[ τ / t ] d2))
  Ihexp[ τ / t ] (d < τ' >) = (Ihexp[ τ / t ] d) < Typ[ τ / t ] τ' >
  Ihexp[ τ / t ] (d ⟨ τ1 ⇒ τ2 ⟩ ) = (Ihexp[ τ / t ] d) ⟨ (Typ[ τ / t ] τ1) ⇒ (Typ[ τ / t ] τ2) ⟩
  Ihexp[ τ / t ] (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = (Ihexp[ τ / t ] d) ⟨ (Typ[ τ / t ] τ1) ⇒⦇-⦈⇏ (Typ[ τ / t ] τ2) ⟩
    
  -- substitution of terms in terms
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
  [ d / y ] ·Λ t d' = ·Λ t ([ d / y ] d')
  [ d / y ] ⦇-⦈⟨ τ ⟩ = ⦇-⦈⟨ τ ⟩
  [ d / y ] ⦇⌜ d' ⌟⦈⟨ τ ⟩ =  ⦇⌜ [ d / y ] d' ⌟⦈⟨ τ ⟩
  [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
  [ d / y ] (d' < τ >) = ([ d / y ] d') < τ >
  [ d / y ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / y ] (d' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩

  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _,_⊢_=>_ : (Θ : typctx) (Γ : tctx) (e : hexp) (τ : htyp) → Set where
      SConst  : {Θ : typctx} {Γ : tctx} → Θ , Γ ⊢ c => b
      SAsc    : {Θ : typctx} {Γ : tctx} {e : hexp} {τ : htyp} →
                 Θ ⊢ τ wf →
                 Θ , Γ ⊢ e <= τ →
                 Θ , Γ ⊢ (e ·: τ) => τ
      SVar    : {Θ : typctx} {Γ : tctx} {τ : htyp} {x : Nat} →
                 (x , τ) ∈ Γ →
                 Θ , Γ ⊢ X x => τ
      SAp     : {Θ : typctx} {Γ : tctx} {e1 e2 : hexp} {τ τ1 τ2 : htyp} →
                 Θ , Γ ⊢ e1 => τ1 →
                 τ1 ▸arr τ2 ==> τ →
                 Θ , Γ ⊢ e2 <= τ2 →
                 Θ , Γ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Θ : typctx} {Γ : tctx} → Θ , Γ ⊢ ⦇-⦈ => ⦇-⦈
      SNEHole : {Θ : typctx} {Γ : tctx} {e : hexp} {τ : htyp} →
                 Θ , Γ ⊢ e => τ →
                 Θ , Γ ⊢ ⦇⌜ e ⌟⦈ => ⦇-⦈
      SLam    : {Θ : typctx} {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 Θ ⊢ τ1 wf →
                 Θ , (Γ ,, (x , τ1)) ⊢ e => τ2 →
                 Θ , Γ ⊢ ·λ x [ τ1 ] e => τ1 ==> τ2
      STLam   : {Θ : typctx} {Γ : tctx} {e : hexp} {t : Nat} {τ : htyp} → 
                (Θ ,, (t , <>)) , Γ ⊢ e => τ → 
                Θ , Γ ⊢ (·Λ t e) => (·∀ t τ)
      STAp    : {Θ : typctx} {Γ : tctx} {e : hexp} {τ1 τ2 τ3 τ4 : htyp} {t : Nat} → 
                Θ ⊢ τ1 wf →
                Θ , Γ ⊢ e => τ2 →
                τ2 ▸forall (·∀ t τ3) →
                Typ[ τ1 / t ] τ3 == τ4 →
                Θ , Γ ⊢ (e < τ1 >) => τ4

    -- analysis
    data _,_⊢_<=_ : (Θ : typctx) (Γ : htyp ctx) (e : hexp) (τ : htyp) → Set where
      ASubsume : {Θ : typctx} {Γ : tctx} {e : hexp} {τ τ' : htyp} →
                 Θ , Γ ⊢ e => τ' →
                 τ ~ τ' →
                 Θ , Γ ⊢ e <= τ
      ALam : {Θ : typctx} {Γ : tctx} {e : hexp} {τ τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 τ ▸arr τ1 ==> τ2 →
                 Θ , (Γ ,, (x , τ1)) ⊢ e <= τ2 →
                 Θ , Γ ⊢ (·λ x e) <= τ
      ATLam : {Θ : typctx} {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {t : Nat} → 
                τ1 ▸forall (·∀ t τ2) → 
                (Θ ,, (t , <>)) , Γ ⊢ e <= τ2 → 
                Θ , Γ ⊢ (·Λ t e) <= τ1

  -- those types without holes
  data _tcomplete : htyp → Set where
    TCBase : b tcomplete
    TCVar : ∀{a} → (T a) tcomplete
    TCArr : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ==> τ2) tcomplete
    TCForall : ∀{t e} → e tcomplete → (·∀ t e) tcomplete 

  -- those external expressions without holes
  data _ecomplete : hexp → Set where
    ECConst : c ecomplete
    ECAsc : ∀{τ e} → τ tcomplete → e ecomplete → (e ·: τ) ecomplete
    ECVar : ∀{x} → (X x) ecomplete
    ECLam1 : ∀{x e} → e ecomplete → (·λ x e) ecomplete
    ECLam2 : ∀{x e τ} → e ecomplete → τ tcomplete → (·λ x [ τ ] e) ecomplete
    ECTLam : ∀{t e} → e ecomplete → (·Λ t e) ecomplete
    ECAp : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECTAp : ∀{τ e} → τ tcomplete → e ecomplete → (e < τ >) ecomplete

  -- those internal expressions without holes
  data _dcomplete : ihexp → Set where
    DCVar : ∀{x} → (X x) dcomplete
    DCConst : c dcomplete
    DCLam : ∀{x τ d} → d dcomplete → τ tcomplete → (·λ x [ τ ] d) dcomplete
    DCTLam : ∀{t d} → d dcomplete → (·Λ t d) dcomplete
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
    CITLam   : ∀{t d} → cast-id d → cast-id (·Λ t d)
    CIHole   : ∀{τ} → cast-id (⦇-⦈⟨ τ ⟩)
    CINEHole : ∀{d τ} → cast-id d → cast-id (⦇⌜ d ⌟⦈⟨ τ ⟩)
    CIAp     : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ∘ d2)
    CITap    : ∀{τ d} → cast-id d → cast-id (d < τ >)
    CICast   : ∀{d τ} → cast-id d → cast-id (d ⟨ τ ⇒ τ ⟩)

  -- expansion
  mutual
    -- synthesis
    data _,_⊢_⇒_~>_ : (Θ : typctx) (Γ : tctx) (e : hexp) (τ : htyp) (d : ihexp) → Set where
      ESConst : ∀{Θ Γ} → Θ , Γ ⊢ c ⇒ b ~> c
      ESVar   : ∀{Θ Γ x τ} → (x , τ) ∈ Γ →
                         Θ , Γ ⊢ X x ⇒ τ ~> X x
      ESLam   : ∀{Θ Γ x τ1 τ2 e d} →
                     (x # Γ) →
                     Θ ⊢ τ1 wf →
                     Θ , (Γ ,, (x , τ1)) ⊢ e ⇒ τ2 ~> d →
                    Θ , Γ ⊢ (·λ x [ τ1 ] e) ⇒ (τ1 ==> τ2) ~> (·λ x [ τ1 ] d)
      ESTLam  : ∀{Θ Γ t e τ d} → 
                (Θ ,, (t , <>)) , Γ ⊢ e ⇒ τ ~> d → 
                Θ , Γ ⊢ (·Λ t e) ⇒ (·∀ t τ) ~> (·Λ t d)
      ESAp : ∀{Θ Γ e1 τ τ1 τ1' τ2 τ2' d1  e2 d2 } →
              Θ , Γ ⊢ e1 => τ1 →
              τ1 ▸arr τ2 ==> τ →
              Θ , Γ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' →
              Θ , Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' →
              Θ , Γ ⊢ (e1 ∘ e2) ⇒ τ ~> ((d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩))
      ESTAp : ∀{Θ Γ e t τ1 τ2 τ3 τ4 τ2' d} →
                Θ ⊢ τ1 wf →
                Θ , Γ ⊢ e => τ2 →
                τ2 ▸forall (·∀ t τ3) →
                Θ , Γ ⊢ e ⇐ (·∀ t τ3) ~> d :: τ2' →
                Typ[ τ1 / t ] τ3 == τ4 →
                Θ , Γ ⊢ (e < τ1 >) ⇒ τ4 ~> ((d ⟨ τ2' ⇒ (·∀ t τ3)⟩) < τ1 >)
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
    data _,_⊢_⇐_~>_::_ : (Θ : typctx) (Γ : tctx) (e : hexp) (τ : htyp) (d : ihexp) (τ' : htyp) → Set where
      EALam : ∀{Θ Γ x τ τ1 τ2 e d τ2'} →
              (x # Γ) →
              τ ▸arr τ1 ==> τ2 →
              Θ , (Γ ,, (x , τ1)) ⊢ e ⇐ τ2 ~> d :: τ2' →
              Θ , Γ ⊢ ·λ x e ⇐ τ ~> ·λ x [ τ1 ] d :: τ1 ==> τ2'
      EATLam : ∀{Θ Γ e t τ1 τ2 τ2' d} → 
                (e ≠ ⦇-⦈) →
                ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈) →
                τ1 ▸forall (·∀ t τ2) → 
                (Θ ,, (t , <>)) , Γ ⊢ e ⇐ τ2 ~> d :: τ2' →
                Θ , Γ ⊢ (·Λ t e) ⇐ τ1 ~> (·Λ t d) :: (·∀ t τ2')
      EASubsume : ∀{e Θ Γ τ' d τ} →
                  (e ≠ ⦇-⦈) →
                  ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈) →
                  Θ , Γ ⊢ e ⇒ τ' ~> d →
                  τ ~ τ' →
                  Θ , Γ ⊢ e ⇐ τ ~> d :: τ'
      EAEHole : ∀{Θ Γ τ} →
                Θ , Γ ⊢ ⦇-⦈ ⇐ τ ~> ⦇-⦈⟨ τ ⟩ :: τ
      EANEHole : ∀{Θ Γ e τ d τ'} →
                 Θ , Γ ⊢ e ⇒ τ' ~> d →
                 Θ , Γ ⊢ ⦇⌜ e ⌟⦈ ⇐ τ ~> ⦇⌜ d ⌟⦈⟨ τ ⟩ :: τ

  -- ground types
  data _ground : (τ : htyp) → Set where
    GBase : b ground
    GArr : ⦇-⦈ ==> ⦇-⦈ ground
    GForall : ∀{t} → ·∀ t ⦇-⦈ ground


  -- type assignment
  data _,_⊢_::_ : (Θ : typctx) (Γ : tctx) (d : ihexp) (τ : htyp) → Set where
    TAConst : ∀{Θ Γ} → Θ , Γ ⊢ c :: b
    TAVar : ∀{Θ Γ x τ} → (x , τ) ∈ Γ → Θ , Γ ⊢ X x :: τ
    TALam : ∀{ Θ Γ x τ1 d τ2} →
            x # Γ →
            Θ ⊢ τ1 wf →
            Θ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
            Θ , Γ ⊢ ·λ x [ τ1 ] d :: (τ1 ==> τ2)
    TATLam : ∀{ Θ Γ t d τ} →
            t # Θ →
            (Θ ,, (t , <>)) , Γ ⊢ d :: τ →
            Θ , Γ ⊢ ·Λ t d :: (·∀ t τ)
    TAAp : ∀{Θ Γ d1 d2 τ1 τ1' τ} →
            Θ , Γ ⊢ d1 :: τ1 ==> τ →
            Θ , Γ ⊢ d2 :: τ1' →
            τ1 =α τ1' →
            Θ , Γ ⊢ d1 ∘ d2 :: τ
    TATAp : ∀ {Θ Γ d t τ1 τ2 τ3} → 
              Θ ⊢ τ1 wf →
              Θ , Γ ⊢ d :: (·∀ t τ2) →
              Typ[ τ1 / t ] τ2 == τ3 → 
              Θ , Γ ⊢ (d < τ1 >) :: τ3
    TAEHole : ∀{Θ Γ τ} →
              Θ , Γ ⊢ ⦇-⦈⟨ τ ⟩ :: τ
    TANEHole : ∀ {Θ Γ d τ} →
              Θ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ τ ⟩ :: τ
    TACast : ∀{Θ Γ d τ1 τ1' τ2} →
            Θ , Γ ⊢ d :: τ1' →
            Θ ⊢ τ2 wf →
            τ1 ~ τ2 →
            τ1 =α τ1' →
            Θ , Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
    TAFailedCast : ∀{Θ Γ d τ1 τ1' τ2} →
            Θ , Γ ⊢ d :: τ1' →
            τ1 ground →
            τ2 ground →
            τ1 ~̸ τ2 →
            τ1 =α τ1' →
            Θ , Γ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ :: τ2

  -- values
  data _val : (d : ihexp) → Set where
    VConst : c val
    VLam   : ∀{x τ d} → (·λ x [ τ ] d) val
    VTLam  : ∀{t d} → (·Λ t d) val

  -- boxed values
  data _boxedval : (d : ihexp) → Set where
    BVVal : ∀{d} → d val → d boxedval
    BVArrCast : ∀{ d τ1 τ2 τ3 τ4 } →
                τ1 ==> τ2 =α̸  τ3 ==> τ4 →
                d boxedval →
                d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ boxedval
    BVForallCast : ∀{ d t1 t2 τ1 τ2 } →
                   (·∀ t1 τ1) =α̸  (·∀ t2 τ2) →
                   d boxedval →
                   d ⟨ (·∀ t1 τ1) ⇒ (·∀ t2 τ2) ⟩ boxedval
    BVHoleCast : ∀{ τ d } → τ ground → d boxedval → d ⟨ τ ⇒ ⦇-⦈ ⟩ boxedval

  mutual
    -- indeterminate forms
    data _indet : (d : ihexp) → Set where
      IEHole : ∀{τ} → ⦇-⦈⟨ τ ⟩ indet
      INEHole : ∀{d τ} → d final → ⦇⌜ d ⌟⦈⟨ τ ⟩ indet
      IAp : ∀{d1 d2} → ((τ1 τ2 τ3 τ4 : htyp) (d1' : ihexp) →
                       d1 ≠ (d1' ⟨(τ1 ==> τ2) ⇒ (τ3 ==> τ4)⟩)) →
                       d1 indet →
                       d2 final →
                       (d1 ∘ d2) indet
      ITAp : ∀{d τ} → ((t1 t2 : Nat) (τ1 τ2 : htyp) (d' : ihexp) →
                       d ≠ (d' ⟨(·∀ t1 τ1) ⇒ (·∀ t2 τ2)⟩)) →
                       d indet →
                       (d < τ >) indet
      ICastArr : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ==> τ2 =α̸  τ3 ==> τ4 →
                 d indet →
                 d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ indet
      ICastForall : ∀{ d t1 t2 τ1 τ2 } →
                   (·∀ t1 τ1) =α̸  (·∀ t2 τ2) →
                   d indet →
                   d ⟨ (·∀ t1 τ1) ⇒ (·∀ t2 τ2) ⟩ indet
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
                    τ1 =α̸  τ2 →
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
    _<_> : ectx → htyp → ectx
    ⦇⌜_⌟⦈⟨_⟩ : ectx → htyp → ectx
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
    ECTAp : ∀{ε t} →
            ε evalctx →
            (ε < t >) evalctx
    ECNEHole : ∀{ε τ} →
               ε evalctx →
               ⦇⌜ ε ⌟⦈⟨ τ ⟩ evalctx
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

  -- matched ground types
  data _▸gnd_ : htyp → htyp → Set where
    MGArr : ∀{τ1 τ2} →
            (τ1 ==> τ2) ≠ (⦇-⦈ ==> ⦇-⦈) →
            (τ1 ==> τ2) ▸gnd (⦇-⦈ ==> ⦇-⦈)
    MGForall : ∀{t τ} →
            (·∀ t τ ≠ ·∀ t ⦇-⦈) →
            (·∀ t τ) ▸gnd (·∀ t ⦇-⦈)

  -- instruction transition judgement
  data _→>_ : (d d' : ihexp) → Set where
    ITLam : ∀{ x τ d1 d2 } →
            -- d2 final → -- red brackets
            ((·λ x [ τ ] d1) ∘ d2) →> ([ d2 / x ] d1)
    ITTLam : ∀{ d t ty } →
              ((·Λ t d) < ty >) →> (Ihexp[ ty / t ] d)
    ITCastID : ∀{d τ1 τ2 } →
               -- d final → -- red brackets
               τ1 =α τ2 →
               (d ⟨ τ1 ⇒ τ2 ⟩) →> d
    ITCastSucceed : ∀{d τ1 τ2 } →
                    -- d final → -- red brackets
                    τ1 ground →
                    τ2 ground →
                    τ1 =α τ2 →
                    (d ⟨ τ1 ⇒ ⦇-⦈ ⇒ τ2 ⟩) →> d
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
    ITTApCast : ∀{d t t' τ τ' ty } →
               -- d final → -- red brackets
               --  ·∀ τ ≠ ·∀ τ' →
                 ((d ⟨ (·∀ t τ) ⇒ (·∀ t' τ')⟩) < ty >) →> ((d < ty >)⟨ Typ[ ty / t ] τ ⇒ Typ[ ty / t' ] τ' ⟩)
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