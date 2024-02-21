open import Prelude
open import Nat
open import debruijn.debruijn-core-type

module debruijn.debruijn-core-exp where

  -- external expressions
  data hexp : Set where
    c       : hexp
    _·:_    : hexp → htyp → hexp
    X       : Nat → hexp
    ·λ      : hexp → hexp
    ·λ[_]_  : htyp → hexp → hexp
    ·Λ      : hexp → hexp
    ⦇-⦈      : hexp
    ⦇⌜_⌟⦈   : hexp → hexp
    _∘_     : hexp → hexp → hexp
    _<_>    : hexp → htyp → hexp

  -- internal expressions
  data ihexp : Set where
    c         : ihexp
    X         : Nat → ihexp
    ·λ[_]_   : htyp → ihexp → ihexp
    ·Λ        : ihexp → ihexp
    ⦇-⦈⟨_⟩     : htyp → ihexp
    ⦇⌜_⌟⦈⟨_⟩    : ihexp → htyp → ihexp
    _∘_       : ihexp → ihexp → ihexp
    _<_>      : ihexp → htyp → ihexp
    _⟨_⇒_⟩    : ihexp → htyp → htyp → ihexp
    _⟨_⇒⦇-⦈⇏_⟩ : ihexp → htyp → htyp → ihexp

  -- convenient notation for chaining together two agreeable casts
  _⟨_⇒_⇒_⟩ : ihexp → htyp → htyp → htyp → ihexp
  d ⟨ t1 ⇒ t2 ⇒ t3 ⟩ = d ⟨ t1 ⇒ t2 ⟩ ⟨ t2 ⇒ t3 ⟩

  -- precision for external expressions
  data _⊑_ : (e1 e2 : hexp) → Set where
    PConst : c ⊑ c
    PVar : ∀{n} → (X n) ⊑ (X n) 
    PAsc : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑t τ2 → (e1 ·: τ1) ⊑ (e2 ·: τ2)
    PEHole : ∀{e} → e ⊑ ⦇-⦈
    PLam1 : ∀{e1 e2} → e1 ⊑ e2 → (·λ e1) ⊑ (·λ e2)
    PLam2 : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑t τ2 → (·λ[ τ1 ] e1) ⊑ (·λ[ τ2 ] e2)
    PTLam : ∀{e1 e2} → e1 ⊑ e2 → (·Λ e1) ⊑ (·Λ e2)
    PNEHole : ∀{e1 e2} → e1 ⊑ e2 → (⦇⌜ e1 ⌟⦈) ⊑ (⦇⌜ e2 ⌟⦈)
    PAp :  ∀{e1 e2 e3 e4} → e1 ⊑ e3 → e2 ⊑ e4 → (e1 ∘ e2) ⊑ (e3 ∘ e4)
    PTAp : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑t τ2 → (e1 < τ1 >) ⊑ (e2 < τ2 >)

  data _subsumable : (e : hexp) → Set where 
    Subsumable : ∀{e} → (e ≠ ⦇-⦈) → ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈) → ((e' : hexp) → e ≠ ·Λ e') → e subsumable

  -- values
  data _val : (d : ihexp) → Set where
    VConst : c val
    VLam   : ∀{τ d} → (·λ[ τ ] d) val
    VTLam  : ∀{d} → (·Λ d) val

  -- boxed values
  data _boxedval : (d : ihexp) → Set where
    BVVal : ∀{d} → 
      d val → 
      d boxedval
    BVArrCast : ∀{ d τ1 τ2 τ3 τ4 } →
      τ1 ==> τ2 ≠ τ3 ==> τ4 →
      d boxedval →
      d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ boxedval
    BVForallCast : ∀{ d τ1 τ2 } →
      (·∀ τ1) ≠ (·∀ τ2) →
      d boxedval →
      d ⟨ (·∀ τ1) ⇒ (·∀ τ2) ⟩ boxedval
    BVHoleCast : ∀{ τ d } → 
      τ ground → 
      d boxedval → 
      d ⟨ τ ⇒ ⦇-⦈ ⟩ boxedval

  mutual
    -- indeterminate forms
    data _indet : (d : ihexp) → Set where
      IEHole : ∀{τ} → 
        ⦇-⦈⟨ τ ⟩ indet
      INEHole : ∀{d τ} → 
        d final → 
        ⦇⌜ d ⌟⦈⟨ τ ⟩ indet
      IAp : ∀{d1 d2} → 
        ((τ1 τ2 τ3 τ4 : htyp) (d1' : ihexp) →
        d1 ≠ (d1' ⟨(τ1 ==> τ2) ⇒ (τ3 ==> τ4)⟩)) →
        d1 indet →
        d2 final →
        (d1 ∘ d2) indet
      ITAp : ∀{d τ} → 
        ((τ1 τ2 : htyp) (d' : ihexp) → d ≠ (d' ⟨(·∀ τ1) ⇒ (·∀ τ2)⟩)) →
        d indet →
        (d < τ >) indet
      ICastArr : ∀{d τ1 τ2 τ3 τ4} →
        τ1 ==> τ2 ≠ τ3 ==> τ4 →
        d indet →
        d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ indet
      ICastForall : ∀{ d τ1 τ2 } →
        (·∀ τ1) ≠ (·∀ τ2) →
        d indet →
        d ⟨ (·∀ τ1) ⇒ (·∀ τ2) ⟩ indet
      ICastGroundHole : ∀{ τ d } →
        τ ground →
        d indet →
        d ⟨ τ ⇒ ⦇-⦈ ⟩ indet
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