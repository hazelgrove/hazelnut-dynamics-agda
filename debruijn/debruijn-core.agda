
open import Prelude
open import Nat
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core-subst

module debruijn.debruijn-core where
  
  data _,_∈_ : Nat → htyp → ctx → Set where 
    InCtxSkip : ∀{Γ τ n} → (n , τ ∈ Γ) → (n , ↑ Z 1 τ ∈ (TVar, Γ)) 
    InCtxZ : ∀{Γ τ} → Z , τ ∈ (τ , Γ)
    InCtx1+ : ∀{Γ τ τ' n} → (n , τ ∈ Γ) → (1+ n , τ ∈ (τ' , Γ)) 

  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : ctx) (e : hexp) (τ : htyp) → Set where
      SConst : {Γ : ctx} → 
        Γ ⊢ c => b
      SAsc : {Γ : ctx} {e : hexp} {τ : htyp} →
        Γ ⊢ τ wf →
        Γ ⊢ e <= τ →
        Γ ⊢ (e ·: τ) => τ
      SVar : {Γ : ctx} {τ : htyp} {n : Nat} →
        n , τ ∈ Γ →
        Γ ⊢ X n => τ
      SAp : {Γ : ctx} {e1 e2 : hexp} {τ τ1 τ2 : htyp} →
        Γ ⊢ e1 => τ1 →
        τ1 ⊓ (⦇-⦈ ==> ⦇-⦈) == τ2 ==> τ →
        Γ ⊢ e2 <= τ2 →
        Γ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Γ : ctx} → 
        Γ ⊢ ⦇-⦈ => ⦇-⦈
      SNEHole : {Γ : ctx} {e : hexp} {τ : htyp} →
        Γ ⊢ e => τ →
        Γ ⊢ ⦇⌜ e ⌟⦈ => ⦇-⦈
      SLam : {Γ : ctx} {e : hexp} {τ1 τ2 : htyp} →
        Γ ⊢ τ1 wf →
        (τ1 , Γ) ⊢ e => τ2 →
        Γ ⊢ ·λ[ τ1 ] e => τ1 ==> τ2
      STLam : {Γ : ctx} {e : hexp} {τ : htyp} → 
        (TVar, Γ) ⊢ e => τ → 
        Γ ⊢ (·Λ e) => (·∀ τ)
      STAp : {Γ : ctx} {e : hexp} {τ1 τ2 τ3 τ4 : htyp} → 
        Γ ⊢ τ1 wf →
        Γ ⊢ e => τ2 →
        τ2 ⊓ ·∀ ⦇-⦈ == (·∀ τ3) →
        TTSub Z τ1 τ3 == τ4 →
        Γ ⊢ (e < τ1 >) => τ4

    -- analysis
    data _⊢_<=_ : (Γ : ctx) (e : hexp) (τ : htyp) → Set where
      ASubsume : {Γ : ctx} {e : hexp} {τ τ' : htyp} →
        Γ ⊢ e => τ' →
        τ ~ τ' →
        Γ ⊢ e <= τ
      ALam : {Γ : ctx} {e : hexp} {τ τ1 τ2 : htyp} →
        τ ⊓ (⦇-⦈ ==> ⦇-⦈) == τ1 ==> τ2 →
        (τ1 , Γ) ⊢ e <= τ2 →
        Γ ⊢ (·λ e) <= τ
      ATLam : {Γ : ctx} {e : hexp} {τ1 τ2 : htyp} → 
        τ1 ⊓ ·∀ ⦇-⦈ == (·∀ τ2) → 
        (TVar, Γ) ⊢ e <= τ2 → 
        Γ ⊢ (·Λ e) <= τ1

  -- bidirectional elaboration judgements
  mutual
    -- synthesis
    data _⊢_⇒_~>_ : (Γ : ctx) (e : hexp) (τ : htyp) (d : ihexp) → Set where
      ESConst : ∀{Γ} → 
        Γ ⊢ c ⇒ b ~> c
      ESVar : ∀{Γ x τ} → 
        x , τ ∈ Γ → 
        Γ ⊢ X x ⇒ τ ~> X x
      ESLam : ∀{Γ τ1 τ2 e d} →
        Γ ⊢ τ1 wf →
        (τ1 , Γ) ⊢ e ⇒ τ2 ~> d →
        Γ ⊢ (·λ[ τ1 ] e) ⇒ (τ1 ==> τ2) ~> (·λ[ τ1 ] d)
      ESTLam : ∀{Γ e τ d} → 
        (e ≠ ⦇-⦈) →
        ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈) →
        (TVar, Γ) ⊢ e ⇒ τ ~> d → 
        Γ ⊢ (·Λ e) ⇒ (·∀ τ) ~> (·Λ d)
      ESAp : ∀{Γ e1 τ τ1 τ1' τ2 τ2' d1  e2 d2 } →
        Γ ⊢ e1 => τ1 →
        τ1 ⊓ (⦇-⦈ ==> ⦇-⦈) == τ2 ==> τ →
        Γ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' →
        Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' →
        Γ ⊢ (e1 ∘ e2) ⇒ τ ~> ((d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩))
      ESTAp : ∀{Γ e τ1 τ2 τ3 τ4 τ2' d} →
        Γ ⊢ τ1 wf →
        Γ ⊢ e => τ2 →
        τ2 ⊓ ·∀ ⦇-⦈ == (·∀ τ3) →
        Γ ⊢ e ⇐ (·∀ τ3) ~> d :: τ2' →
        TTSub Z τ1 τ3 == τ4 →
        Γ ⊢ (e < τ1 >) ⇒ τ4 ~> ((d ⟨ τ2' ⇒ (·∀ τ3)⟩) < τ1 >)
      ESEHole : ∀{Γ} →
        Γ ⊢ ⦇-⦈ ⇒ ⦇-⦈ ~> ⦇-⦈
      ESNEHole : ∀{Γ e τ d} →
        Γ ⊢ e ⇒ τ ~> d →
        Γ ⊢ ⦇⌜ e ⌟⦈ ⇒ ⦇-⦈ ~> ⦇⌜ d ⌟⦈
      ESAsc : ∀ {Γ e τ d τ'} →
        Γ ⊢ τ wf →
        Γ ⊢ e ⇐ τ ~> d :: τ' →
        Γ ⊢ (e ·: τ) ⇒ τ ~> (d ⟨ τ' ⇒ τ ⟩)

    -- analysis
    data _⊢_⇐_~>_::_ : (Γ : ctx) (e : hexp) (τ : htyp) (d : ihexp) (τ' : htyp) → Set where
      EALam : ∀{Γ τ τ1 τ2 e d τ2'} →
        τ ⊓ (⦇-⦈ ==> ⦇-⦈) == τ1 ==> τ2 →
        (τ1 , Γ) ⊢ e ⇐ τ2 ~> d :: τ2' →
        Γ ⊢ ·λ e ⇐ τ ~> ·λ[ τ1 ] d :: τ1 ==> τ2'
      EATLam : ∀{Γ e τ1 τ2 τ2' d} → 
        τ1 ⊓ ·∀ ⦇-⦈ == (·∀ τ2) → 
        (TVar, Γ) ⊢ e ⇐ τ2 ~> d :: τ2' →
        Γ ⊢ (·Λ e) ⇐ τ1 ~> (·Λ d) :: (·∀ τ2')
      EASubsume : ∀{e Γ τ1 τ2 τ3 d} →
        e subsumable →
        Γ ⊢ e ⇒ τ2 ~> d →
        τ1 ⊓ τ2 == τ3 →
        Γ ⊢ e ⇐ τ1 ~> (d ⟨ τ2 ⇒ τ3 ⟩) :: τ3

  -- type assignment
  data _⊢_::_ : (Γ : ctx) (d : ihexp) (τ : htyp) → Set where
    TAConst : ∀{Γ} → 
      Γ ⊢ c :: b
    TAVar : ∀{Γ n τ} → 
      n , τ ∈ Γ → 
      Γ ⊢ X n :: τ
    TALam : ∀{ Γ τ1 d τ2} →
      Γ ⊢ τ1 wf →
      (τ1 , Γ) ⊢ d :: τ2 →
      Γ ⊢ ·λ[ τ1 ] d :: (τ1 ==> τ2)
    TATLam : ∀{ Γ d τ} →
      (TVar, Γ) ⊢ d :: τ →
      Γ ⊢ ·Λ d :: (·∀ τ)
    TAAp : ∀{Γ d1 d2 τ1 τ} →
      Γ ⊢ d1 :: τ1 ==> τ →
      Γ ⊢ d2 :: τ1 →
      Γ ⊢ d1 ∘ d2 :: τ
    TATAp : ∀ {Γ d τ1 τ2 τ3} → 
      Γ ⊢ τ1 wf →
      Γ ⊢ d :: (·∀ τ2) →
      TTSub Z τ1 τ2 == τ3 → 
      Γ ⊢ (d < τ1 >) :: τ3
    TAEHole : ∀{Γ} →
      Γ ⊢ ⦇-⦈ :: ⦇-⦈
    TANEHole : ∀ {Γ d τ} →
      Γ ⊢ d :: τ →
      Γ ⊢ ⦇⌜ d ⌟⦈ :: ⦇-⦈
    TACast : ∀{Γ d τ1 τ2} →
      Γ ⊢ d :: τ1 →
      Γ ⊢ τ2 wf →
      τ1 ~ τ2 →
      Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
    TAFailedCast : ∀{Γ d τ1 τ2} →
      Γ ⊢ d :: τ1 →
      τ1 ground →
      τ2 ground →
      τ1 ~̸ τ2 →
      Γ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ :: τ2

  -- precision for internal expressions
  -- see Refined Criteria for Gradual Typing, Figure 9
  data _,_⊢_⊑i_ : (Γ : ctx) → (Γ' : ctx) → (d1 d2 : ihexp) → Set where
    PIConst : ∀{Γ Γ'} → Γ , Γ' ⊢ c ⊑i c
    PIVar : ∀{Γ Γ' n} → Γ , Γ' ⊢ (X n) ⊑i (X n) 
    PIEHole : ∀{Γ Γ' d} → Γ , Γ' ⊢ d ⊑i ⦇-⦈
    PILam : ∀{Γ Γ' d1 d2 τ1 τ2} → (τ1 , Γ) , (τ2 , Γ') ⊢ d1 ⊑i d2 → τ1 ⊑t τ2 → Γ , Γ' ⊢ (·λ[ τ1 ] d1) ⊑i (·λ[ τ2 ] d2)
    PITLam : ∀{Γ Γ' d1 d2} → (TVar, Γ) , Γ' ⊢ d1 ⊑i d2 → Γ , Γ' ⊢ (·Λ d1) ⊑i (·Λ d2)
    PINEHole : ∀{Γ Γ' d1 d2} → Γ , Γ' ⊢ d1 ⊑i d2 → Γ , Γ' ⊢ ⦇⌜ d1 ⌟⦈ ⊑i ⦇⌜ d2 ⌟⦈
    PIAp :  ∀{Γ Γ' d1 d2 d3 d4} → Γ , Γ' ⊢ d1 ⊑i d3 → Γ , Γ' ⊢ d2 ⊑i d4 → Γ , Γ' ⊢ (d1 ∘ d2) ⊑i (d3 ∘ d4)
    PITAp : ∀{Γ Γ' d1 d2 τ1 τ2} → Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ2 → Γ , Γ' ⊢ (d1 < τ1 >) ⊑i (d2 < τ2 >)
    PICast : ∀{Γ Γ' d1 d2 τ1 τ2 τ3 τ4} → Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ3 → τ2 ⊑t τ4 → Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒ τ4 ⟩)
    PIFailedCast : ∀{Γ Γ' d1 d2 τ1 τ2 τ3 τ4} → Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ3 → τ2 ⊑t τ4 → Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒⦇-⦈⇏ τ4 ⟩)
    PIRemoveCast : ∀{Γ Γ' d1 d2 τ1 τ2 τ} → (Γ , Γ' ⊢ d1 ⊑i d2) → (Γ' ⊢ d2 :: τ) → (τ1 ⊑t τ) → (τ2 ⊑t τ) → Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒ τ2 ⟩) ⊑i d2 
    PIAddCast : ∀{Γ Γ' d1 d2 τ1 τ2 τ} → (Γ , Γ' ⊢ d1 ⊑i d2) → (Γ ⊢ d1 :: τ) → (τ ⊑t τ1) → (τ ⊑t τ2) → Γ , Γ' ⊢ d1 ⊑i (d2 ⟨ τ1 ⇒ τ2 ⟩) 
    PIBlame : ∀{Γ Γ' d1 d2 τ1 τ2 τ} → (Γ' ⊢ d2 :: τ) → (τ2 ⊑t τ) → (Γ , Γ' ⊢ d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ⊑i d2)

  -- evaluation contexts
  data ectx : Set where
    ⊙ : ectx
    _∘₁_ : ectx → ihexp → ectx
    _∘₂_ : ihexp → ectx → ectx
    _<_> : ectx → htyp → ectx
    ⦇⌜_⌟⦈ : ectx → ectx
    _⟨_⇒_⟩ : ectx → htyp → htyp → ectx
    _⟨_⇒⦇-⦈⇏_⟩ : ectx → htyp → htyp → ectx

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
    FHNEHole : ∀{ d d' ε} →
              d == ε ⟦ d' ⟧ →
              ⦇⌜ d ⌟⦈ ==  ⦇⌜ ε ⌟⦈ ⟦ d' ⟧
    FHCast : ∀{ d d' ε τ1 τ2 } →
            d == ε ⟦ d' ⟧ →
            d ⟨ τ1 ⇒ τ2 ⟩ == ε ⟨ τ1 ⇒ τ2 ⟩ ⟦ d' ⟧
    FHFailedCast : ∀{ d d' ε τ1 τ2} →
            d == ε ⟦ d' ⟧ →
            (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) == (ε ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⟦ d' ⟧

  -- instruction transition judgement
  data _→>_ : (d d' : ihexp) → Set where
    ITLam : ∀{ τ d1 d2 } →
            -- d2 final → -- red brackets
            ((·λ[ τ ] d1) ∘ d2) →> (ttSub Z Z d2 d1)
    ITTLam : ∀{ d τ } →
              ((·Λ d) < τ >) →> (TtSub Z τ d)
    ITCastID : ∀{ d τ } →
               -- d final → -- red brackets
               (d ⟨ τ ⇒ τ ⟩) →> d
    ITCastSucceed : ∀{ d τ } →
                    -- d final → -- red brackets
                    τ ground →
                    (d ⟨ τ ⇒ ⦇-⦈ ⇒ τ ⟩) →> d
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
    ITTApCast : ∀{ d τ1 τ2 τ3 } →
               -- d final → -- red brackets
               --  ·∀ τ ≠ ·∀ τ' →
                 ((d ⟨ (·∀ τ1) ⇒ (·∀ τ2)⟩) < τ3 >) →> ((d < τ3 >)⟨ TTSub Z τ3 τ1 ⇒ TTSub Z τ3 τ2 ⟩)
    ITGround : ∀{ d τ τ'} →
               -- d final → -- red brackets
               τ ▸gnd τ' →
               (d ⟨ τ ⇒ ⦇-⦈ ⟩) →> (d ⟨ τ ⇒ τ' ⇒ ⦇-⦈ ⟩)
    ITExpand : ∀{ d τ τ' } →
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

  -- those types without holes
  data _tcomplete : htyp → Set where
    TCBase : b tcomplete
    TCVar : ∀{n} → (T n) tcomplete
    TCArr : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ==> τ2) tcomplete
    TCForall : ∀{e} → e tcomplete → (·∀ e) tcomplete 

  -- those external expressions without holes
  data _ecomplete : hexp → Set where
    ECConst : c ecomplete
    ECAsc : ∀{τ e} → τ tcomplete → e ecomplete → (e ·: τ) ecomplete
    ECVar : ∀{x} → (X x) ecomplete
    ECLam1 : ∀{e} → e ecomplete → (·λ e) ecomplete
    ECLam2 : ∀{e τ} → e ecomplete → τ tcomplete → (·λ[ τ ] e) ecomplete
    ECTLam : ∀{e} → e ecomplete → (·Λ e) ecomplete
    ECAp : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECTAp : ∀{τ e} → τ tcomplete → e ecomplete → (e < τ >) ecomplete

  -- those internal expressions without holes
  data _dcomplete : ihexp → Set where
    DCVar : ∀{x} → (X x) dcomplete
    DCConst : c dcomplete
    DCLam : ∀{τ d} → d dcomplete → τ tcomplete → (·λ[ τ ] d) dcomplete
    DCTLam : ∀{d} → d dcomplete → (·Λ d) dcomplete
    DCAp : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → (d1 ∘ d2) dcomplete
    DCTAp : ∀{τ d} → τ tcomplete → d dcomplete → (d < τ >) dcomplete
    DCCast : ∀{d τ1 τ2} → d dcomplete → τ1 tcomplete → τ2 tcomplete → (d ⟨ τ1 ⇒ τ2 ⟩) dcomplete

  data _dcompleteid : ihexp → Set where
    DCVar : ∀{x} → (X x) dcompleteid
    DCConst : c dcompleteid
    DCLam : ∀{τ d} → d dcompleteid → τ tcomplete → (·λ[ τ ] d) dcompleteid
    DCTLam : ∀{d} → d dcompleteid → (·Λ d) dcompleteid
    DCAp : ∀{d1 d2} → d1 dcompleteid → d2 dcompleteid → (d1 ∘ d2) dcompleteid
    DCTAp : ∀{τ d} → τ tcomplete → d dcompleteid → (d < τ >) dcompleteid
    DCCast : ∀{d τ} → d dcompleteid → τ tcomplete → (d ⟨ τ ⇒ τ ⟩) dcompleteid

  -- contexts that only produce complete types
  data _gcomplete : ctx → Set where
    GCEmpty : ∅ gcomplete
    GCVar : ∀{Γ τ} → Γ gcomplete → τ tcomplete → (τ , Γ) gcomplete
    GCTVar : ∀{Γ} → Γ gcomplete → (TVar, Γ) gcomplete

  -- -- those internal expressions where every cast is the identity cast and
  -- -- there are no failed casts
  -- data cast-id : ihexp → Set where
  --   CIConst  : cast-id c
  --   CIVar    : ∀{x} → cast-id (X x)
  --   CILam    : ∀{x τ d} → cast-id d → cast-id (·λ x [ τ ] d)
  --   CITLam   : ∀{t d} → cast-id d → cast-id (·Λ t d)
  --   CIHole   : ∀{τ} → cast-id (⦇-⦈⟨ τ ⟩)
  --   CINEHole : ∀{d τ} → cast-id d → cast-id (⦇⌜ d ⌟⦈⟨ τ ⟩)
  --   CIAp     : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ∘ d2)
  --   CITap    : ∀{τ d} → cast-id d → cast-id (d < τ >)
  --   CICast   : ∀{d τ} → cast-id d → cast-id (d ⟨ τ ⇒ τ ⟩)
 