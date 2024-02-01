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