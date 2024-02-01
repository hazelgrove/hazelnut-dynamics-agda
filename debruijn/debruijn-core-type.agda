open import Prelude
open import Nat

module debruijn.debruijn-core-type where

  -- types
  data htyp : Set where
    b     : htyp
    T     : Nat → htyp
    ⦇-⦈    : htyp
    _==>_ : htyp → htyp → htyp
    ·∀    : htyp → htyp

  -- arrow type constructors bind very tightly
  infixr 25  _==>_

  data _~_ : htyp → htyp → Set where 
    ConsistBase : b ~ b
    ConsistVar : ∀ {x} → T x ~ T x
    ConsistHole1 : ∀ {τ} → τ ~ ⦇-⦈
    ConsistHole2 : ∀ {τ} → ⦇-⦈ ~ τ
    ConsistArr : ∀ {τ1 τ2 τ3 τ4} → τ1 ==> τ2 ~ τ3 ==> τ4
    ConsistForall : ∀ {τ1 τ2} → τ1 ~ τ2 → ·∀ τ1 ~ ·∀ τ2

  -- type inconsistency
  _~̸_ : (t1 t2 : htyp) → Set
  _~̸_ = \(t1 t2 : htyp) → ¬(t1 ~ t2)

  data _⊑t_ : htyp → htyp → Set where 
    PTBase : b ⊑t b 
    PTHole : ∀{τ} → τ ⊑t ⦇-⦈     
    PTTVar : ∀{n} → (T n) ⊑t (T n) 
    PTArr : ∀{τ1 τ2 τ3 τ4} → τ1 ⊑t τ3 → τ2 ⊑t τ4 → (τ1 ==> τ2) ⊑t (τ3 ==> τ4) 
    PTForall : ∀{τ1 τ2} → τ1 ⊑t τ2 → (·∀ τ1) ⊑t (·∀ τ2) 

  data _⊓_==_ : htyp → htyp → htyp → Set where 
    JoinHoleL : ∀ {τ} → ⦇-⦈ ⊓ τ == τ
    JoinHoleR : ∀ {τ} → τ ⊓ ⦇-⦈ == τ
    JoinBase : b ⊓ b == b
    JoinVar : ∀ {x} → T x ⊓ T x == T x
    JoinArr : ∀ {τ1 τ2 τ3 τ4 τ5 τ6} → τ1 ⊓ τ3 == τ5 → τ2 ⊓ τ4 == τ6 → τ1 ==> τ2 ⊓ τ3 ==> τ4 == τ5 ==> τ6
    JoinForall : ∀ {τ1 τ2 τ3} → τ1 ⊓ τ2 == τ3 → ·∀ τ1 ⊓ ·∀ τ2 == ·∀ τ3 
  
  --- matching for arrows
  data _▸arr_ : htyp → htyp → Set where
    MAHole : ⦇-⦈ ▸arr ⦇-⦈ ==> ⦇-⦈
    MAArr  : {τ1 τ2 : htyp} → τ1 ==> τ2 ▸arr τ1 ==> τ2

  --- matching for foralls
  data _▸forall_ : htyp → htyp → Set where
    MFHole : ⦇-⦈ ▸forall (·∀ ⦇-⦈)
    MFForall : ∀{τ} → (·∀ τ) ▸forall (·∀ τ)

  -- ground types
  data _ground : (τ : htyp) → Set where
    GBase : b ground
    GArr : ⦇-⦈ ==> ⦇-⦈ ground
    GForall : ·∀ ⦇-⦈ ground

  -- matched ground types
  data _▸gnd_ : htyp → htyp → Set where
    MGArr : ∀{τ1 τ2} →
      (τ1 ==> τ2) ≠ (⦇-⦈ ==> ⦇-⦈) →
      (τ1 ==> τ2) ▸gnd (⦇-⦈ ==> ⦇-⦈)
    MGForall : ∀{τ} →
      (·∀ τ ≠ ·∀ ⦇-⦈) →
      (·∀ τ) ▸gnd (·∀ ⦇-⦈)

  -- the type of type contexts i.e. Θs in the judgements below
  typctx : Set
  typctx = Nat
  
  -- well-formedness of types
  data _⊢_wf : typctx → htyp → Set where
    WFVarZ : ∀{n} → 1+ n ⊢ T Z wf
    WFVarS : ∀{n m} → n ⊢ T m wf → 1+ n ⊢ T (1+ m) wf
    WFBase : ∀{Θ} → Θ ⊢ b wf
    WFHole : ∀{Θ} → Θ ⊢ ⦇-⦈ wf
    WFArr : ∀{Θ τ1 τ2} → Θ ⊢ τ1 wf → Θ ⊢ τ2 wf → Θ ⊢ τ1 ==> τ2 wf
    WFForall : ∀{Θ τ} → 1+ Θ ⊢ τ wf → Θ ⊢ ·∀ τ wf

  -- the type of term to type contexts, i.e. Γs in the judegments below
  data ctx : Set where 
    ∅ : ctx
    _,_ : htyp → ctx → ctx

  -- well-formedness of contexts
  data _⊢_ctxwf : typctx → ctx → Set where
    CtxWFEmpty : ∀{Θ} → Θ ⊢ ∅ ctxwf
    CtxWFExtend : ∀{Θ Γ τ} → Θ ⊢ τ wf → Θ ⊢ Γ ctxwf → Θ ⊢ τ , Γ ctxwf

  data _,_∈_ : Nat → htyp → ctx → Set where 
    InCtxZ : ∀{Γ τ} → Z , τ ∈ (τ , Γ)
    InCtx1+ : ∀{Γ τ τ' n} → (n , τ ∈ Γ) → (1+ n , τ ∈ (τ' , Γ)) 

  data _⊑c_ : ctx → ctx → Set where 
    PCEmpty : ∅ ⊑c ∅ 
    PCExtend : ∀{τ Γ τ' Γ'} → (τ ⊑t τ') → (Γ ⊑c Γ') → ((τ , Γ) ⊑c (τ' , Γ'))
    