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
    ConsistArr : ∀ {τ1 τ2 τ3 τ4} → τ1 ~ τ3 → τ2 ~ τ4 → τ1 ==> τ2 ~ τ3 ==> τ4
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
    MeetHoleL : ∀ {τ} → ⦇-⦈ ⊓ τ == τ
    MeetHoleR : ∀ {τ} → τ ⊓ ⦇-⦈ == τ
    MeetBase : b ⊓ b == b
    MeetVar : ∀ {x} → T x ⊓ T x == T x
    MeetArr : ∀ {τ1 τ2 τ3 τ4 τ5 τ6} → τ1 ⊓ τ3 == τ5 → τ2 ⊓ τ4 == τ6 → τ1 ==> τ2 ⊓ τ3 ==> τ4 == τ5 ==> τ6
    MeetForall : ∀ {τ1 τ2 τ3} → τ1 ⊓ τ2 == τ3 → ·∀ τ1 ⊓ ·∀ τ2 == ·∀ τ3 
  
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

  -- the type of term to type contexts, i.e. Γs in the judegments below
  data ctx : Set where 
    ∅ : ctx
    _,_ : htyp → ctx → ctx
    TVar,_ : ctx → ctx

  infixr 18 TVar,_

  _ctx+_ : ctx → ctx → ctx 
  ∅ ctx+ ctx2 = ctx2
  (x , ctx1) ctx+ ctx2 = (x , ctx1 ctx+ ctx2)
  (TVar, ctx1) ctx+ ctx2 = (TVar, ctx1 ctx+ ctx2)

  ctx-extend-tvars : Nat → ctx → ctx 
  ctx-extend-tvars Z Γ = Γ
  ctx-extend-tvars (1+ n) Γ = (TVar, ctx-extend-tvars n Γ)

  -- data _⊢_varwf : ctx → Nat → Set where
  --   WFSkip : ∀{Γ τ} → Γ ⊢ Z varwf → (τ , Γ) ⊢ Z varwf
  --   WFVarZ : ∀{Γ} → (TVar, Γ) ⊢ Z varwf
  --   WFVarS : ∀{Γ n} → Γ ⊢ n varwf → (TVar, Γ) ⊢ (1+ n) varwf

  -- well-formedness of types
  data _⊢_wf : ctx → htyp → Set where
    -- WFVar : ∀{Γ n} → Γ ⊢ n varwf → Γ ⊢ T n wf
    WFSkip : ∀{Γ n τ} → Γ ⊢ T n wf → (τ , Γ) ⊢ T n wf
    WFVarZ : ∀{Γ} → (TVar, Γ) ⊢ T Z wf
    WFVarS : ∀{Γ n} → Γ ⊢ T n wf → (TVar, Γ) ⊢ T (1+ n) wf
    WFBase : ∀{Γ} → Γ ⊢ b wf
    WFHole : ∀{Γ} → Γ ⊢ ⦇-⦈ wf
    WFArr : ∀{Γ τ1 τ2} → Γ ⊢ τ1 wf → Γ ⊢ τ2 wf → Γ ⊢ τ1 ==> τ2 wf
    WFForall : ∀{Γ τ} → (TVar, Γ) ⊢ τ wf → Γ ⊢ ·∀ τ wf

  -- well-formedness of contexts
  data ⊢_ctxwf : ctx → Set where
    CtxWFEmpty : ⊢ ∅ ctxwf
    CtxWFVar : ∀{Γ τ} → Γ ⊢ τ wf → ⊢ Γ ctxwf → ⊢ τ , Γ ctxwf
    CtxWFTVar : ∀{Γ} → ⊢ Γ ctxwf → ⊢ (TVar, Γ) ctxwf

  -- Not accurate: domains may not be equal
  data _⊑c_ : ctx → ctx → Set where 
    PCEmpty : ∅ ⊑c ∅ 
    PCVar : ∀{τ Γ τ' Γ'} → (τ ⊑t τ') → (Γ ⊑c Γ') → ((τ , Γ) ⊑c (τ' , Γ'))
    PCTVar : ∀{Γ Γ'} → (Γ ⊑c Γ') → ((TVar, Γ) ⊑c (TVar, Γ'))
  
  data context-counter : ctx → Nat → Nat → Set where 
    CtxCtEmpty : context-counter ∅ Z Z 
    CtxCtVar : ∀{Γ n m τ} → context-counter Γ n m → context-counter (τ , Γ) (1+ n) m 
    CtxCtTVar : ∀{Γ n m} → context-counter Γ n m → context-counter (TVar, Γ) n (1+ m) 