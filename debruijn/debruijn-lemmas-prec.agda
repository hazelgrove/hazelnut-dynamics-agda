open import Nat
open import Prelude
open import contexts
open import debruijn.debruijn-core

module debruijn.debruijn-lemmas-prec where

  ⊑t-refl : (τ : htyp) → τ ⊑t τ
  ⊑t-refl b = PTBase 
  ⊑t-refl (T x) = PTTVar
  ⊑t-refl ⦇-⦈ = PTHole
  ⊑t-refl (τ ==> τ₁) = PTArr (⊑t-refl τ) (⊑t-refl τ₁)
  ⊑t-refl (·∀ τ) = PTForall (⊑t-refl τ)