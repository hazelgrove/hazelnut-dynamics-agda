
open import Nat
open import Prelude
open import contexts

module core where

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
    ⦇-⦈[_]   : Nat → hexp
    ⦇⌜_⌟⦈[_]  : hexp → Nat → hexp
    _∘_     : hexp → hexp → hexp
    _<_>    : hexp → htyp → hexp

  -- the type of type contexts, i.e. Γs in the judegments below
  tctx : Set
  tctx = htyp ctx

  -- the type of "type contexts" (name collision with above), containing 
  -- all type variables in scope, i.e. Θs in the judgements below
  typctx : Set
  typctx = ⊤ ctx

  -- the type of hole contexts, i.e. Δs in the judgements
  hctx : Set
  hctx = (typctx × htyp ctx × htyp) ctx

  -- notation for a triple to match the CMTT syntax
  _::_[_,_] : Nat → htyp → typctx → tctx → (Nat × (typctx × tctx × htyp))
  u :: τ [ Θ , Γ ] = u , (Θ , Γ , τ)

  module alpha where 

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

  open alpha

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
  
  mutual

    -- identity substitution, substitition environments
    -- for term variables and terms:
    data env : Set where
      Id : (Γ : tctx) → env
      Subst : (d : ihexp) → (y : Nat) → env → env
    -- for type variables and types:
    data typenv : Set where
      TypId : (Θ : typctx) → typenv
      TypSubst : (τ : htyp) → (t : Nat) → typenv → typenv

    -- internal expressions
    data ihexp : Set where
      c         : ihexp
      X         : Nat → ihexp
      ·λ_[_]_   : Nat → htyp → ihexp → ihexp
      ·Λ        : Nat → ihexp → ihexp
      ⦇-⦈⟨_⟩     : (Nat × typenv × env) → ihexp
      ⦇⌜_⌟⦈⟨_⟩    : ihexp → (Nat × typenv × env) → ihexp
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
    WFForall : ∀{Θ n t} → (Θ ,, (n , <>)) ⊢ t wf → Θ ⊢ ·∀ n t wf

  -- well-formedness of contexts
  data _⊢_tctxwf : typctx → tctx → Set where
    CCtx : ∀{Θ Γ} → (∀{x y} → (x , y) ∈ Γ → Θ ⊢ y wf) → Θ ⊢ Γ tctxwf

  -- well-formedness of hole contexts
  data _hctxwf : hctx → Set where
    HCtx : ∀{Δ} → (∀ {x Θ Γ τ} → (x , (Θ , Γ , τ)) ∈ Δ → ((Θ ⊢ Γ tctxwf) × (Θ ⊢ τ wf))) → Δ hctxwf

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
    HNTLam : ∀{t e u} → 
             hole-name-new e u → 
             hole-name-new (·Λ t e) u
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
    HDTLam : ∀{t e1 e2} → holes-disjoint e1 e2 → holes-disjoint (·Λ t e1) e2
    HDHole : ∀{u e2} → hole-name-new e2 u → holes-disjoint (⦇-⦈[ u ]) e2
    HDNEHole : ∀{u e1 e2} → hole-name-new e2 u → holes-disjoint e1 e2 → holes-disjoint (⦇⌜ e1 ⌟⦈[ u ]) e2
    HDAp :  ∀{e1 e2 e3} → holes-disjoint e1 e3 → holes-disjoint e2 e3 → holes-disjoint (e1 ∘ e2) e3
    HDTAp : ∀{e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (e1 < τ >) e2

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
  
  Hctx[_/_]_ : htyp → Nat → hctx → hctx
  Hctx[ tau / t ] sigma = map (\(theta , gamma , tau') → (theta , (Tctx[ tau / t ] gamma) , tau')) sigma

  {-
  TypSub[_/_]_ : htyp -> Nat -> typenv -> typenv
  TypSub[ tau / t ] (TypId theta) = (TypId theta) --TODO: Might need to change keys in theta?
  TypSub[ tau / t ] (TypSubst tau' t' theta) = 
  -}
  
  mutual
    -- substitution of types in terms 
    Ihexp[_/_]_ : htyp → Nat → ihexp → ihexp
    Ihexp[ τ / t ] c = c
    Ihexp[ τ / t ] (X x) = X x
    Ihexp[ τ / t ] (·λ x [ τx ] d) = ·λ x [ Typ[ τ / t ] τx ] (Ihexp[ τ / t ] d)
    Ihexp[ τ / t ] (·Λ t' d) with natEQ t t'
    ... | Inl refl = (·Λ t' d)
    ... | Inr neq = (·Λ t' (Ihexp[ τ / t ] d))
    Ihexp[ τ / t ] (⦇-⦈⟨ u , θ , σ ⟩) = ⦇-⦈⟨ u , TypSubst τ t θ , Sub[ τ / t ] σ ⟩
    Ihexp[ τ / t ] (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩) = ⦇⌜ (Ihexp[ τ / t ] d) ⌟⦈⟨ u , TypSubst τ t θ , Sub[ τ / t ] σ ⟩
    Ihexp[ τ / t ] (d1 ∘ d2) = ((Ihexp[ τ / t ] d1) ∘ (Ihexp[ τ / t ] d2))
    Ihexp[ τ / t ] (d < τ' >) = (Ihexp[ τ / t ] d) < Typ[ τ / t ] τ' >
    Ihexp[ τ / t ] (d ⟨ τ1 ⇒ τ2 ⟩ ) = (Ihexp[ τ / t ] d) ⟨ (Typ[ τ / t ] τ1) ⇒ (Typ[ τ / t ] τ2) ⟩
    Ihexp[ τ / t ] (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = (Ihexp[ τ / t ] d) ⟨ (Typ[ τ / t ] τ1) ⇒⦇-⦈⇏ (Typ[ τ / t ] τ2) ⟩
    
    -- substitution of types in environments
    Sub[_/_]_ : htyp → Nat → env → env
    Sub[ tau / t ] (Id gamma) = Id (Tctx[ tau / t ] gamma)
    Sub[ tau / t ] (Subst d y sigma) = Subst (Ihexp[ tau / t ] d) y (Sub[ tau / t ] sigma)
  
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
  [ d / y ] ⦇-⦈⟨ u , θ , σ ⟩ = ⦇-⦈⟨ u , θ , Subst d y σ ⟩
  [ d / y ] ⦇⌜ d' ⌟⦈⟨ u , θ , σ  ⟩ =  ⦇⌜ [ d / y ] d' ⌟⦈⟨ u , θ , Subst d y σ ⟩
  [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
  [ d / y ] (d' < τ >) = ([ d / y ] d') < τ >
  [ d / y ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / y ] (d' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩

  -- applying an environment to an expression
  apply-env : env → ihexp → ihexp
  apply-env (Id Γ) d = d
  apply-env (Subst d y σ) d' = [ d / y ] ( apply-env σ d')

  -- applying a type environment to a type
  apply-typenv : typenv → htyp → htyp
  apply-typenv (TypId Θ) τ = τ
  apply-typenv (TypSubst τ y θ) τ' = Typ[ τ / y ] ( apply-typenv θ τ')
  
  -- applying a type environment to a tctx
  apply-typenv-env : typenv → tctx → tctx
  apply-typenv-env (TypId Θ) Γ = Γ
  apply-typenv-env (TypSubst τ y θ) Γ = Tctx[ τ / y ] ( apply-typenv-env θ Γ)

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
                 holes-disjoint e1 e2 →
                 Θ , Γ ⊢ e1 => τ1 →
                 τ1 ▸arr τ2 ==> τ →
                 Θ , Γ ⊢ e2 <= τ2 →
                 Θ , Γ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Θ : typctx} {Γ : tctx} {u : Nat} → Θ , Γ ⊢ ⦇-⦈[ u ] => ⦇-⦈
      SNEHole : {Θ : typctx} {Γ : tctx} {e : hexp} {τ : htyp} {u : Nat} →
                 hole-name-new e u →
                 Θ , Γ ⊢ e => τ →
                 Θ , Γ ⊢ ⦇⌜ e ⌟⦈[ u ] => ⦇-⦈
      SLam    : {Θ : typctx} {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 Θ ⊢ τ1 wf →
                 Θ , (Γ ,, (x , τ1)) ⊢ e => τ2 →
                 Θ , Γ ⊢ ·λ x [ τ1 ] e => τ1 ==> τ2
      STLam   : {Θ : typctx} {Γ : tctx} {e : hexp} {t : Nat} {τ : htyp} → 
                -- t # Θ → -- See note in TATLam
                (Θ ,, (t , <>)) , Γ ⊢ e => τ → 
                Θ , Γ ⊢ (·Λ t e) => (·∀ t τ)
      STAp    : {Θ : typctx} {Γ : tctx} {e : hexp} {τ1 τ2 τ3 τ4 : htyp} {t : Nat} → 
                -- t # Θ →
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
    CIHole   : ∀{u} → cast-id (⦇-⦈⟨ u ⟩)
    CINEHole : ∀{d u} → cast-id d → cast-id (⦇⌜ d ⌟⦈⟨ u ⟩)
    CIAp     : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ∘ d2)
    CITap    : ∀{τ d} → cast-id d → cast-id (d < τ >)
    CICast   : ∀{d τ} → cast-id d → cast-id (d ⟨ τ ⇒ τ ⟩)

  -- expansion
  mutual
    -- synthesis
    data _,_⊢_⇒_~>_⊣_ : (Θ : typctx) (Γ : tctx) (e : hexp) (τ : htyp) (d : ihexp) (Δ : hctx) → Set where
      ESConst : ∀{Θ Γ} → Θ , Γ ⊢ c ⇒ b ~> c ⊣ ∅
      ESVar   : ∀{Θ Γ x τ} → (x , τ) ∈ Γ →
                         Θ , Γ ⊢ X x ⇒ τ ~> X x ⊣ ∅
      ESLam   : ∀{Θ Γ x τ1 τ2 e d Δ} →
                     (x # Γ) →
                     Θ ⊢ τ1 wf →
                     Θ , (Γ ,, (x , τ1)) ⊢ e ⇒ τ2 ~> d ⊣ Δ →
                    Θ , Γ ⊢ ·λ x [ τ1 ] e ⇒ (τ1 ==> τ2) ~> ·λ x [ τ1 ] d ⊣ Δ
      ESTLam  : ∀{Θ Γ t e τ d Δ} → 
                -- t # Θ →
                (Θ ,, (t , <>)) , Γ ⊢ e ⇒ τ ~> d ⊣ Δ → 
                Θ , Γ ⊢ (·Λ t e) ⇒ (·∀ t τ) ~> (·Λ t d) ⊣ Δ
      ESAp : ∀{Θ Γ e1 τ τ1 τ1' τ2 τ2' d1 Δ1 e2 d2 Δ2} →
              holes-disjoint e1 e2 →
              Δ1 ## Δ2 →
              Θ , Γ ⊢ e1 => τ1 →
              τ1 ▸arr τ2 ==> τ →
              Θ , Γ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' ⊣ Δ1 →
              Θ , Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
              Θ , Γ ⊢ e1 ∘ e2 ⇒ τ ~> (d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩) ⊣ (Δ1 ∪ Δ2)
      ESTAp : ∀{Θ Γ e t τ1 τ2 τ3 τ4 τ2' d Δ} → -- TODO: Check that we don't need more binders
                Θ ⊢ τ1 wf →
                Θ , Γ ⊢ e => τ2 →
                τ2 ▸forall (·∀ t τ3) →
                Θ , Γ ⊢ e ⇐ (·∀ t τ3) ~> d :: τ2' ⊣ Δ →
                Typ[ τ1 / t ] τ3 == τ4 →
                Θ , Γ ⊢ (e < τ1 >) ⇒ τ4 ~> (d ⟨ τ2' ⇒ (·∀ t τ3)⟩) < τ1 > ⊣ Δ
      ESEHole : ∀{Θ Γ u} →
                Θ , Γ ⊢ ⦇-⦈[ u ] ⇒ ⦇-⦈ ~> ⦇-⦈⟨ u , TypId Θ , Id Γ ⟩ ⊣  ■ (u :: ⦇-⦈ [ Θ , Γ ])
      ESNEHole : ∀{Θ Γ e τ d u Δ} →
                 Δ ## (■ (u , Θ , Γ , ⦇-⦈)) →
                 Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                 Θ , Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇒ ⦇-⦈ ~> ⦇⌜ d ⌟⦈⟨ u , TypId Θ , Id Γ ⟩ ⊣ (Δ ,, u :: ⦇-⦈ [ Θ , Γ ])
      ESAsc : ∀ {Θ Γ e τ d τ' Δ} →
                 Θ ⊢ τ wf →
                 Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                 Θ , Γ ⊢ (e ·: τ) ⇒ τ ~> d ⟨ τ' ⇒ τ ⟩ ⊣ Δ

    -- analysis
    data _,_⊢_⇐_~>_::_⊣_ : (Θ : typctx) (Γ : tctx) (e : hexp) (τ : htyp) (d : ihexp) (τ' : htyp) (Δ : hctx) → Set where
      EALam : ∀{Θ Γ x τ τ1 τ2 e d τ2' Δ } →
              (x # Γ) →
              τ ▸arr τ1 ==> τ2 →
              Θ , (Γ ,, (x , τ1)) ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
              Θ , Γ ⊢ ·λ x e ⇐ τ ~> ·λ x [ τ1 ] d :: τ1 ==> τ2' ⊣ Δ
      EATLam : ∀{Θ Γ e t τ1 τ2 τ2' d Δ} → 
                ((u : Nat) → e ≠ ⦇-⦈[ u ]) →
                ((e' : hexp) (u : Nat) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
                τ1 ▸forall (·∀ t τ2) → 
                (Θ ,, (t , <>)) , Γ ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
                Θ , Γ ⊢ (·Λ t e) ⇐ τ1 ~> (·Λ t d) :: (·∀ t τ2') ⊣ Δ
      EASubsume : ∀{e Θ Γ τ' d Δ τ} →
                  ((u : Nat) → e ≠ ⦇-⦈[ u ]) →
                  ((e' : hexp) (u : Nat) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
                  Θ , Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  τ ~ τ' →
                  Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
      EAEHole : ∀{Θ Γ u τ} →
                Θ , Γ ⊢ ⦇-⦈[ u ] ⇐ τ ~> ⦇-⦈⟨ u , TypId Θ , Id Γ ⟩ :: τ ⊣ ■ (u :: τ [ Θ , Γ ])
      EANEHole : ∀{Θ Γ e u τ d τ' Δ} →
                 Δ ## (■ (u , Θ , Γ , τ)) →
                 Θ , Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                 Θ , Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇐ τ ~> ⦇⌜ d ⌟⦈⟨ u , TypId Θ , Id Γ ⟩ :: τ ⊣ (Δ ,, u :: τ [ Θ , Γ ])

  -- ground types
  data _ground : (τ : htyp) → Set where
    GBase : b ground
    -- GVar : ∀{a} → (T a) ground
    GArr : ⦇-⦈ ==> ⦇-⦈ ground
    GForall : ∀{t} → ·∀ t ⦇-⦈ ground

  mutual
    -- substitution typing
    -- WARNING - TODO: these rules are provisional and not verified with respect
    -- to the fill and resume semantics. Need re-examination when hole contexts
    -- are added to the implementation or used in the mechanization.
    data _,_,_⊢_,_:s:_,_ : hctx → typctx → tctx → typenv → env → typctx → tctx → Set where
      STAIdId : ∀{Γ Γ' Δ Θ Θ'} →
                  ((x : Nat) (τ : htyp) → (x , τ) ∈ Γ' → (x , τ) ∈ Γ) →
                  ((τ : htyp) → Θ' ⊢ τ wf → Θ ⊢ τ wf) →
                  Δ , Θ , Γ ⊢ TypId Θ' , Id Γ' :s: Θ' , Γ'
      STAIdSubst : ∀{Γ Γ' y τ d σ Δ Θ Θ'} →
                  Δ , Θ , (Γ ,, (y , τ)) ⊢ TypId Θ' , σ :s: Θ' , Γ' →
                  Δ , Θ , Γ ⊢ d :: τ →
                  Δ , Θ , Γ ⊢ TypId Θ' , Subst d y σ :s: Θ' , Γ'
      STASubst : ∀{Θ Θ' Γ Δ θ σ y Γ' τ } →
               Δ , (Θ ,, (y , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' →
               ∅ ⊢ τ wf →
               Δ , Θ , Γ ⊢ TypSubst τ y θ , σ :s: Θ' , Γ'

    -- type assignment
    data _,_,_⊢_::_ : (Δ : hctx) (Θ : typctx) (Γ : tctx) (d : ihexp) (τ : htyp) → Set where
      TAConst : ∀{Δ Θ Γ} → Δ , Θ , Γ ⊢ c :: b
      TAVar : ∀{Δ Θ Γ x τ} → (x , τ) ∈ Γ → Δ , Θ , Γ ⊢ X x :: τ
      TALam : ∀{ Δ Θ Γ x τ1 d τ2} →
              x # Γ →
              Θ ⊢ τ1 wf →
              Δ , Θ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
              Δ , Θ , Γ ⊢ ·λ x [ τ1 ] d :: (τ1 ==> τ2)
      TATLam : ∀{ Δ Θ Γ t d τ} →
              t # Θ →
              Δ , Θ ,, (t , <>) , Γ ⊢ d :: τ →
              Δ , Θ , Γ ⊢ ·Λ t d :: (·∀ t τ)
      TAAp : ∀{Δ Θ Γ d1 d2 τ1 τ1' τ} →
             Δ , Θ , Γ ⊢ d1 :: τ1 ==> τ →
             Δ , Θ , Γ ⊢ d2 :: τ1' →
             τ1 =α τ1' →
             Δ , Θ , Γ ⊢ d1 ∘ d2 :: τ
      TATAp : ∀ {Δ Θ Γ d t τ1 τ2 τ3} → 
                Θ ⊢ τ1 wf →
                Δ , Θ , Γ ⊢ d :: (·∀ t τ2) →
                Typ[ τ1 / t ] τ2 == τ3 → 
                Δ , Θ , Γ ⊢ (d < τ1 >) :: τ3
      TAEHole : ∀{Δ Θ Γ θ σ u Θ' Γ' Γ'' τ τ'} →
                (u , (Θ' , Γ' , τ')) ∈ Δ →
                Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ'' →
                τ == apply-typenv θ τ' →
                Γ'' == apply-typenv-env θ Γ' →
                Δ , Θ , Γ ⊢ ⦇-⦈⟨ u , θ , σ ⟩ :: τ
      TANEHole : ∀ {Δ Θ Γ d τ'' u Θ' Γ' Γ'' θ σ τ τ'} →
                 (u , (Θ' , Γ' , τ')) ∈ Δ →
                 Δ , Θ , Γ ⊢ d :: τ'' →
                 Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ'' →
                 τ == apply-typenv θ τ' →
                 Γ'' == apply-typenv-env θ Γ' →
                 Δ , Θ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩ :: τ
      TACast : ∀{Δ Θ Γ d τ1 τ1' τ2} →
             Δ , Θ , Γ ⊢ d :: τ1' →
             Θ ⊢ τ2 wf →
             τ1 ~ τ2 →
             τ1 =α τ1' →
             Δ , Θ , Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
      TAFailedCast : ∀{Δ Θ Γ d τ1 τ1' τ2} →
             Δ , Θ , Γ ⊢ d :: τ1' →
             τ1 ground →
             τ2 ground →
             τ1 ~̸ τ2 →
             τ1 =α τ1' →
             Δ , Θ , Γ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ :: τ2

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
      IEHole : ∀{u θ σ} → ⦇-⦈⟨ u , θ , σ ⟩ indet
      INEHole : ∀{d u θ σ} → d final → ⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩ indet
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
    ⦇⌜_⌟⦈⟨_⟩ : ectx → (Nat × typenv × env ) → ectx
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
    ECNEHole : ∀{ε u θ σ} →
               ε evalctx →
               ⦇⌜ ε ⌟⦈⟨ u , θ , σ ⟩ evalctx
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
    FHNEHole : ∀{ d d' ε u θ σ} →
              d == ε ⟦ d' ⟧ →
              ⦇⌜ d ⌟⦈⟨ (u , θ , σ ) ⟩ ==  ⦇⌜ ε ⌟⦈⟨ (u , θ , σ ) ⟩ ⟦ d' ⟧
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

  -- freshness
  mutual
    -- ... with respect to a hole context
    data envfresh : Nat → env → Set where
      EFId : ∀{x Γ} → x # Γ → envfresh x (Id Γ)
      EFSubst : ∀{x d σ y} → fresh x d
                           → envfresh x σ
                           → x ≠ y
                           → envfresh x (Subst d y σ)
    

    data tfresh-in-Γ : Nat → tctx → Set where
      TFΓ : ∀{x Γ} → ((x' : Nat) (y : htyp) → ((x' , y) ∈ Γ) → tfresht x y) → tfresh-in-Γ x Γ
    
    data envtfresh : Nat → env → Set where
      ETFId : ∀{x Γ} → tfresh-in-Γ x Γ → envtfresh x (Id Γ)
      ETFSubst : ∀{x d σ y} → tfresh x d
                           → envtfresh x σ
                           → x ≠ y
                           → envtfresh x (Subst d y σ)

    data tenvtfresh : Nat → typenv → Set where
      TETFId : ∀{t θ} → t # θ → tenvtfresh t (TypId θ)
      TETFSubst : ∀{t τ θ t'} → tfresht t τ
                           → tenvtfresh t θ
                           → t ≠ t'
                           → tenvtfresh t (TypSubst τ t' θ)

    -- ... for internal expressions
    data fresh : Nat → ihexp → Set where
      FConst : ∀{x} → fresh x c
      FVar   : ∀{x y} → x ≠ y → fresh x (X y)
      FLam   : ∀{x y τ d} → x ≠ y → fresh x d → fresh x (·λ y [ τ ] d)
      FTLam  : ∀{x t d} → fresh x d → fresh x (·Λ t d)
      FHole  : ∀{x u θ σ} → envfresh x σ → fresh x (⦇-⦈⟨ u , θ , σ ⟩)
      FNEHole : ∀{x d u θ σ} → envfresh x σ → fresh x d → fresh x (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      FAp     : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x (d1 ∘ d2)
      FTAp    : ∀{x τ d} → fresh x d → fresh x (d < τ >)
      FCast   : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒ τ2 ⟩)
      FFailedCast : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  -- In reference to type variables
    data tfresht : Nat → htyp → Set where
     TFBase   : ∀{x} → tfresht x b
     TFTVar    : ∀{x t} → x ≠ t → tfresht x (T t)
     TFHole   : ∀{x} → tfresht x ⦇-⦈
     TFArr    : ∀{x t1 t2} → tfresht x t1 → tfresht x t2 → tfresht x (t1 ==> t2)
     TFForall : ∀{x t t'} → x ≠ t → tfresht x t' → tfresht x (·∀ t t')
     
    data tfresh : Nat → ihexp → Set where
      TFConst : ∀{x} → tfresh x c
      TFVar   : ∀{x y} → tfresh x (X y)
      TFLam   : ∀{x y τ d} → tfresht x τ → tfresh x d →  tfresh x (·λ y [ τ ] d)
      TFTLam  : ∀{x t d} → x ≠ t → tfresh x d → tfresh x (·Λ t d)
      TFHole  : ∀{x u θ σ} → envtfresh x σ → tenvtfresh x θ → tfresh x (⦇-⦈⟨ u , θ , σ ⟩)
      TFNEHole : ∀{x d u θ σ} → envtfresh x σ → tenvtfresh x θ → tfresh x d → tfresh x (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      TFAp     : ∀{x d1 d2} → tfresh x d1 → tfresh x d2 → tfresh x (d1 ∘ d2)
      TFTAp    : ∀{x τ d} → tfresht x τ → tfresh x d → tfresh x (d < τ >)
      TFCast   : ∀{x d τ1 τ2} → tfresh x d → tfresh x (d ⟨ τ1 ⇒ τ2 ⟩)
      TFFailedCast : ∀{x d τ1 τ2} → tfresh x d → tfresh x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  
  -- ... for external expressions
  data freshh : Nat → hexp → Set where
    FRHConst : ∀{x} → freshh x c
    FRHAsc   : ∀{x e τ} → freshh x e → freshh x (e ·: τ)
    FRHVar   : ∀{x y} → x ≠ y → freshh x (X y)
    FRHLam1  : ∀{x y e} → x ≠ y → freshh x e → freshh x (·λ y e)
    FRHLam2  : ∀{x τ e y} → x ≠ y → freshh x e → freshh x (·λ y [ τ ] e)
    FRHTLam  : ∀{x t e} → freshh x e → freshh x (·Λ t e)
    FRHEHole : ∀{x u} → freshh x (⦇-⦈[ u ])
    FRHNEHole : ∀{x u e} → freshh x e → freshh x (⦇⌜ e ⌟⦈[ u ])
    FRHAp : ∀{x e1 e2} → freshh x e1 → freshh x e2 → freshh x (e1 ∘ e2)
    FRHTAp    : ∀{x τ e} → freshh x e → freshh x (e < τ >)

  -- x is not used in a binding site in d
  mutual
  
    data unbound-in-σ : Nat → env → Set where
      UBσId : ∀{x Γ} → unbound-in-σ x (Id Γ)
      UBσSubst : ∀{x d y σ} → unbound-in x d
                            → unbound-in-σ x σ
                            → x ≠ y
                            → unbound-in-σ x (Subst d y σ)
    
    data tunbound-in-Δ : Nat → hctx → Set where
      UBΔ : ∀{t Δ} → ((u : Nat) (Θ : typctx) (Γ : tctx) (τ : htyp) → ((u , Θ , Γ , τ) ∈ Δ) → tunboundt-in t τ) → tunbound-in-Δ t Δ

    data tunbound-in-Γ : Nat → tctx → Set where
      UBΓ : ∀{t Γ} → ((x : Nat) (y : htyp) → ((x , y) ∈ Γ) → tunboundt-in t y) → tunbound-in-Γ t Γ
  
    data tunbound-in-σ : Nat → env → Set where
      TUBσId : ∀{x Γ} → tunbound-in-σ x (Id Γ)
      TUBσSubst : ∀{x d y σ} → tunbound-in x d
                            → tunbound-in-σ x σ
                            → tunbound-in-σ x (Subst d y σ)
    
    data tunbound-in-θ : Nat → typenv → Set where
      UBθId : ∀{t Γ} → tunbound-in-θ t (TypId Γ)
      UBθSubst : ∀{t τ y θ} → tunboundt-in t τ
                            → tunbound-in-θ t θ
                            → tunbound-in-θ t (TypSubst τ y θ)

    data unbound-in : (x : Nat) (d : ihexp) → Set where
      UBConst : ∀{x} → unbound-in x c
      UBVar : ∀{x y} → unbound-in x (X y)
      UBLam2 : ∀{x d y τ} → x ≠ y
                           → unbound-in x d
                           → unbound-in x (·λ_[_]_ y τ d)
      UBTLam : ∀{x t d} → unbound-in x d → unbound-in x (·Λ t d)
      UBHole : ∀{x u θ σ} → unbound-in-σ x σ
                         → unbound-in x (⦇-⦈⟨ u , θ , σ ⟩)
      UBNEHole : ∀{x u θ σ d }
                  → unbound-in-σ x σ
                  → unbound-in x d
                  → unbound-in x (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      UBAp : ∀{ x d1 d2 } →
            unbound-in x d1 →
            unbound-in x d2 →
            unbound-in x (d1 ∘ d2)
      UBTAp : ∀{x τ d} → unbound-in x d → unbound-in x (d < τ >)
      UBCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒ τ2 ⟩)
      UBFailedCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
      
    data tunbound-in : (t : Nat) → (d : ihexp) → Set where
      TUBConst : ∀{t} → tunbound-in t c
      TUBVar : ∀{t y} → tunbound-in t (X y)
      TUBLam2 : ∀{t d y τ} → tunbound-in t d
                           → tunboundt-in t τ
                           → tunbound-in t (·λ_[_]_ y τ d)
      TUBTLam : ∀{t t' τ} → t ≠ t' → tunbound-in t τ → tunbound-in t (·Λ t' τ)
      TUBHole : ∀{t u θ σ} → tunbound-in-θ t θ
                         → tunbound-in-σ t σ
                         → tunbound-in t (⦇-⦈⟨ u , θ , σ ⟩)
      TUBNEHole : ∀{t u θ σ d }
                  → tunbound-in-θ t θ
                  → tunbound-in-σ t σ
                  → tunbound-in t d
                  → tunbound-in t (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      TUBAp : ∀{ t d1 d2 } →
            tunbound-in t d1 →
            tunbound-in t d2 →
            tunbound-in t (d1 ∘ d2)
      TUBTAp : ∀{t τ d} → tunbound-in t d → tunboundt-in t τ → tunbound-in t (d < τ >)
      TUBCast : ∀{t d τ1 τ2} → tunbound-in t d →
                               tunboundt-in t τ1 →
                               tunboundt-in t τ2 →
                               tunbound-in t (d ⟨ τ1 ⇒ τ2 ⟩)
      TUBFailedCast : ∀{t d τ1 τ2} → tunbound-in t d →
                               tunboundt-in t τ1 →
                               tunboundt-in t τ2 →
                               tunbound-in t (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
    
    data tunboundt-in : (t : Nat) → (τ : htyp) → Set where
      UBBase : ∀{t} → tunboundt-in t b
      UBTVar : ∀{t t'} → tunboundt-in t (T t')
      UBHole : ∀{t} → tunboundt-in t ⦇-⦈
      UBArr : ∀{t τ1 τ2} → tunboundt-in t τ1 → tunboundt-in t τ2 → tunboundt-in t (τ1 ==> τ2)
      UBForall : ∀{t t' τ} → t ≠ t' → tunboundt-in t τ → tunboundt-in t (·∀ t' τ)
      


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
      BDTLam :  ∀{t d1 d2} → binders-disjoint d1 d2
                          → binders-disjoint (·Λ t d1) d2
      BDHole : ∀{u θ σ d2} → binders-disjoint-σ σ d2
                         → binders-disjoint (⦇-⦈⟨ u , θ , σ ⟩) d2
      BDNEHole : ∀{u σ θ d1 d2} → binders-disjoint-σ σ d2
                                → binders-disjoint d1 d2
                                → binders-disjoint (⦇⌜ d1 ⌟⦈⟨ u , θ , σ ⟩) d2
      BDAp :  ∀{d1 d2 d3} → binders-disjoint d1 d3
                          → binders-disjoint d2 d3
                          → binders-disjoint (d1 ∘ d2) d3
      BDTAp : ∀{d1 d2 τ} → binders-disjoint d1 d2
                          → binders-disjoint (d1 < τ >) d2
      BDCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒ τ2 ⟩) d2
      BDFailedCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) d2
      
    data tbinderst-disjoint-Δ : hctx -> htyp -> Set where
      TBDΔ : ∀{τ Δ} → 
        ((u : Nat) (Θ : typctx) (Γ : tctx) (τ' : htyp) → ((u , Θ , Γ , τ') ∈ Δ) → 
        tbinderstt-disjoint τ' τ × tbinderst-disjoint-Γ Γ τ) → tbinderst-disjoint-Δ Δ τ
    
    data tbinders-disjoint-Δ : hctx -> ihexp -> Set where
      TBDΔConst : ∀{Δ} → tbinders-disjoint-Δ Δ c
      TBDΔVar : ∀{x Δ} → tbinders-disjoint-Δ Δ (X x)
      TBDΔLam : ∀{x τ d Δ} → tbinders-disjoint-Δ Δ d
                            → tbinderst-disjoint-Δ Δ τ
                            → tbinders-disjoint-Δ Δ (·λ_[_]_ x τ d)
      TBDΔTLam :  ∀{t Δ d} → tbinders-disjoint-Δ Δ d
                          → tunbound-in-Δ t Δ
                          → tbinders-disjoint-Δ Δ (·Λ t d)
      BDΔHole : ∀{u θ σ Δ} → tbinders-disjoint-Δ Δ (⦇-⦈⟨ u , θ , σ ⟩)
        {- Could all tb-d between theta and sigma if needed) -}
      TBDΔNEHole : ∀{u σ θ Δ d} → tbinders-disjoint-Δ Δ d
                                → tbinders-disjoint-Δ Δ (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      TBDΔAp :  ∀{Δ d1 d2} → tbinders-disjoint-Δ Δ d1
                          → tbinders-disjoint-Δ Δ d2
                          → tbinders-disjoint-Δ Δ (d1 ∘ d2)
      TBDΔTAp : ∀{Δ d τ} → tbinders-disjoint-Δ Δ d
                           → tbinderst-disjoint-Δ Δ τ
                          → tbinders-disjoint-Δ Δ (d < τ >)
      TBDΔCast : ∀{Δ d τ1 τ2} → tbinders-disjoint-Δ Δ d
                           → tbinderst-disjoint-Δ Δ τ1
                           → tbinderst-disjoint-Δ Δ τ2
                           → tbinders-disjoint-Δ Δ (d ⟨ τ1 ⇒ τ2 ⟩)
      TBDΔFailedCast : ∀{Δ d τ1 τ2} → tbinders-disjoint-Δ Δ d
                           → tbinderst-disjoint-Δ Δ τ1
                           → tbinderst-disjoint-Δ Δ τ2
                           → tbinders-disjoint-Δ Δ (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
    
    data tbinderst-disjoint-Γ : tctx -> htyp -> Set where
      TBDΔ : ∀{τ Γ} → 
        ((x : Nat) (τ' : htyp) → ((x , τ') ∈ Γ) → 
        tbinderstt-disjoint τ' τ) → tbinderst-disjoint-Γ Γ τ
        
    data tbinders-disjoint-Γ : tctx -> ihexp -> Set where
      TBDΓConst : ∀{Γ} → tbinders-disjoint-Γ Γ c
      TBDΓVar : ∀{x Γ} → tbinders-disjoint-Γ Γ (X x)
      TBDΓLam : ∀{x τ d Γ} → tbinders-disjoint-Γ Γ d
                            → tbinderst-disjoint-Γ Γ τ
                            → tbinders-disjoint-Γ Γ (·λ_[_]_ x τ d)
      TBDΓTLam :  ∀{t Γ d} → tbinders-disjoint-Γ Γ d
                          → tunbound-in-Γ t Γ
                          → tbinders-disjoint-Γ Γ (·Λ t d)
      BDΓHole : ∀{u θ σ Γ} → tbinders-disjoint-Γ Γ (⦇-⦈⟨ u , θ , σ ⟩)
        {- Could all tb-d between theta and sigma if needed) -}
      TBDΓNEHole : ∀{u σ θ Γ d} → tbinders-disjoint-Γ Γ d
                                → tbinders-disjoint-Γ Γ (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      TBDΓAp :  ∀{Γ d1 d2} → tbinders-disjoint-Γ Γ d1
                          → tbinders-disjoint-Γ Γ d2
                          → tbinders-disjoint-Γ Γ (d1 ∘ d2)
      TBDΓTAp : ∀{Γ d τ} → tbinders-disjoint-Γ Γ d
                           → tbinderst-disjoint-Γ Γ τ
                          → tbinders-disjoint-Γ Γ (d < τ >)
      TBDΓCast : ∀{Γ d τ1 τ2} → tbinders-disjoint-Γ Γ d
                           → tbinderst-disjoint-Γ Γ τ1
                           → tbinderst-disjoint-Γ Γ τ2
                           → tbinders-disjoint-Γ Γ (d ⟨ τ1 ⇒ τ2 ⟩)
      TBDΓFailedCast : ∀{Γ d τ1 τ2} → tbinders-disjoint-Γ Γ d
                           → tbinderst-disjoint-Γ Γ τ1
                           → tbinderst-disjoint-Γ Γ τ2
                           → tbinders-disjoint-Γ Γ (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
    
    data tbinders-disjoint-σ : env → ihexp → Set where
      BDσId : ∀{Γ d} → tbinders-disjoint-σ (Id Γ) d
      BDσSubst : ∀{d1 d2 y σ} → tbinders-disjoint d1 d2
                              → tbinders-disjoint-σ σ d2
                              → tbinders-disjoint-σ (Subst d1 y σ) d2
      
    data tbinders-disjoint-θ : typenv → ihexp → Set where
      BDTθId : ∀{Θ d} → tbinders-disjoint-θ (TypId Θ) d
      BDTθSubst : ∀{τ d t θ} → tbinderst-disjoint τ d
               → tbinders-disjoint-θ θ d
               → tbinders-disjoint-θ (TypSubst τ t θ) d
               
    data tbinderst-disjoint-θ : typenv → htyp → Set where
      BDTθId : ∀{Θ τ} → tbinderst-disjoint-θ (TypId Θ) τ
      BDTθSubst : ∀{τ τ' t θ} → tbinderstt-disjoint τ τ'
               → tbinderst-disjoint-θ θ τ'
               → tbinderst-disjoint-θ (TypSubst τ t θ) τ'
               
    data tbinders-disjoint-θ-σ : typenv → env → Set where
      BDTθId : ∀{Θ σ} → tbinders-disjoint-θ-σ (TypId Θ) σ
      BDTθSubst : ∀{τ t θ σ} → tunbound-in-σ t σ
               → tbinders-disjoint-θ-σ θ σ
               → tbinders-disjoint-θ-σ (TypSubst τ t θ) σ
    
    data tbinderst-disjoint : htyp → ihexp → Set where
      TBDTConst : ∀{τ} → tbinderst-disjoint τ c
      TBDTVar : ∀{x τ} → tbinderst-disjoint τ (X x)
      TBDTLam : ∀{x τ τ' d} → tbinderstt-disjoint τ τ'
                            → tbinderst-disjoint τ (·λ_[_]_ x τ' d)
      TBDTTLam :  ∀{t τ d} → tbinderst-disjoint τ d
                            → tunboundt-in t τ
                            → tbinderst-disjoint τ (·Λ t d)
      TBDTHole : ∀{u τ θ σ} → tbinderst-disjoint-θ θ τ
                            → tbinderst-disjoint τ (⦇-⦈⟨ u , θ , σ ⟩)
      TBDTNEHole : ∀{u τ σ θ d} → tbinderst-disjoint-θ θ τ
                                → tbinderst-disjoint τ d
                                → tbinderst-disjoint τ (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      TBDTAp :  ∀{τ d1 d2} → tbinderst-disjoint τ d1
                          → tbinderst-disjoint τ d2
                          → tbinderst-disjoint τ (d1 ∘ d2)
      TBDTTAp : ∀{τ τ' d} → tbinderst-disjoint τ d
                          -> tbinderstt-disjoint τ τ'
                          → tbinderst-disjoint τ (d < τ' >)
      TBDTCast : ∀{τ d τ1 τ2} → tbinderst-disjoint τ d → tbinderstt-disjoint τ τ1 -> tbinderstt-disjoint τ τ2 -> tbinderst-disjoint τ (d ⟨ τ1 ⇒ τ2 ⟩)
      TBDTFailedCast : ∀{τ d τ1 τ2} → tbinderst-disjoint τ d → tbinderstt-disjoint τ τ1 -> tbinderstt-disjoint τ τ2 -> tbinderst-disjoint τ (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
               
    data tbinderstt-disjoint : htyp → htyp → Set where
      BDTBase : ∀{τ} → tbinderstt-disjoint b τ
      BDTTVar : ∀{τ t} → tbinderstt-disjoint (T t) τ
      BDTHole :  ∀{τ} → tbinderstt-disjoint ⦇-⦈ τ
      BDTArr : ∀{τ1 τ2 τ} → tbinderstt-disjoint τ1 τ
                         → tbinderstt-disjoint τ2 τ
                         → tbinderstt-disjoint (τ1 ==> τ2) τ
      BDTForall : ∀{t τ' τ} → tbinderstt-disjoint τ' τ
                           → tunboundt-in t τ
                           → tbinderstt-disjoint (·∀ t τ') τ
      
    data tbinders-disjoint : (d1 : ihexp) → (d2 : ihexp) → Set where
      TBDConst : ∀{d} → tbinders-disjoint c d
      TBDVar : ∀{x d} → tbinders-disjoint (X x) d
      TBDLam : ∀{x τ d1 d2} → tbinders-disjoint d1 d2
                            → tbinders-disjoint (·λ_[_]_ x τ d1) d2
      TBDTLam :  ∀{t d1 d2} → tbinders-disjoint d1 d2
                            → tunbound-in t d2
                            → tbinders-disjoint (·Λ t d1) d2
      TBDHole : ∀{u θ σ d2} → tbinders-disjoint-θ θ d2
                            → tbinders-disjoint (⦇-⦈⟨ u , θ , σ ⟩) d2
      TBDNEHole : ∀{u σ θ d1 d2} → tbinders-disjoint-θ θ d2
                                → tbinders-disjoint d1 d2
                                → tbinders-disjoint (⦇⌜ d1 ⌟⦈⟨ u , θ , σ ⟩) d2
      TBDAp :  ∀{d1 d2 d3} → tbinders-disjoint d1 d3
                          → tbinders-disjoint d2 d3
                          → tbinders-disjoint (d1 ∘ d2) d3
      TBDTAp : ∀{d1 d2 τ} → tbinders-disjoint d1 d2
                          → tbinders-disjoint (d1 < τ >) d2
      TBDCast : ∀{d1 d2 τ1 τ2} → tbinders-disjoint d1 d2 → tbinders-disjoint (d1 ⟨ τ1 ⇒ τ2 ⟩) d2
      TBDFailedCast : ∀{d1 d2 τ1 τ2} → tbinders-disjoint d1 d2 → tbinders-disjoint (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) d2
      
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
      BUTLam : ∀{t d} → binders-unique d
                       → binders-unique (·Λ t d)
      BUEHole : ∀{u θ σ} → binders-unique-σ σ
                        → binders-unique (⦇-⦈⟨ u , θ , σ ⟩)
      BUNEHole : ∀{u σ θ d} → binders-unique d
                           → binders-unique-σ σ
                           → binders-unique (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      BUAp : ∀{d1 d2} → binders-unique d1
                       → binders-unique d2
                       → binders-disjoint d1 d2
                       → binders-unique (d1 ∘ d2)
      BUTAp : ∀{d τ} → binders-unique d
                       → binders-unique (d < τ >)
      BUCast : ∀{d τ1 τ2} → binders-unique d
                           → binders-unique (d ⟨ τ1 ⇒ τ2 ⟩)
      BUFailedCast : ∀{d τ1 τ2} → binders-unique d
                                 → binders-unique (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
    
    data tbinders-unique-θ : typenv → Set where
      BUθId : ∀{Θ} → tbinders-unique-θ (TypId Θ)
      BUθSubst : ∀{τ t θ} → tbinderst-unique τ
                          → tbinders-unique-θ θ
                          → tbinderst-disjoint-θ θ τ
                          → tbinders-unique-θ (TypSubst τ t θ)
    
    data tbinders-unique-σ : env → Set where
      TBUσId : ∀{Γ} → tbinders-unique-σ (Id Γ)
      TBUσSubst : ∀{d y σ} → tbinders-unique d
                          → tbinders-unique-σ σ
                          → tbinders-disjoint-σ σ d
                          → tbinders-unique-σ (Subst d y σ)
    
    data tbinderst-unique : htyp → Set where
      BUBase : tbinderst-unique b
      BUTVar : ∀{t} → tbinderst-unique (T t)
      BUHole :  tbinderst-unique ⦇-⦈
      BUArr : ∀{τ1 τ2} → tbinderst-unique τ1
                       → tbinderst-unique τ2
                       → tbinderstt-disjoint τ1 τ2
                       → tbinderst-unique (τ1 ==> τ2)
      BUForall : ∀{t τ} → tbinderst-unique τ
                         → tunboundt-in t τ
                         → tbinderst-unique (·∀ t τ)
    
    data tbinders-unique : ihexp → Set where
      TBUHole : tbinders-unique c
      TBUVar : ∀{x} → tbinders-unique (X x)
      TBULam : {x : Nat} {τ : htyp} {d : ihexp} → tbinders-unique d
                                                → tbinders-unique (·λ_[_]_ x τ d)
      TBUTLam : ∀{t d} → tbinders-unique d
                       → tunbound-in t d
                       → tbinders-unique (·Λ t d)
      TBUEHole : ∀{u θ σ} → tbinders-unique-θ θ
                          → tbinders-unique-σ σ
                          → tbinders-disjoint-θ-σ θ σ
                          → tbinders-unique (⦇-⦈⟨ u , θ , σ ⟩)
      TBUNEHole : ∀{u σ θ d} → tbinders-unique d
                           → tbinders-unique-θ θ
                           → tbinders-unique-σ σ
                           → tbinders-disjoint-θ-σ θ σ
                           → tbinders-unique (⦇⌜ d ⌟⦈⟨ u , θ , σ ⟩)
      TBUAp : ∀{d1 d2} → tbinders-unique d1
                       → tbinders-unique d2
                       → tbinders-disjoint d1 d2
                       → tbinders-unique (d1 ∘ d2)
      TBUTAp : ∀{d τ} → tbinders-unique d
                      → tbinderst-unique τ
                      → tbinderst-disjoint τ d
                       → tbinders-unique (d < τ >)
      TBUCast : ∀{d τ1 τ2} → tbinders-unique d
                           → tbinders-unique (d ⟨ τ1 ⇒ τ2 ⟩)
      TBUFailedCast : ∀{d τ1 τ2} → tbinders-unique d
                                 → tbinders-unique (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
