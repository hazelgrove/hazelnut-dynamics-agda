
open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core

module debruijn.debruijn-lemmas-ctx where

  extend-tvar-comm : (n : Nat) → (Γ : ctx) → ctx-extend-tvars n (TVar, Γ) == (TVar, ctx-extend-tvars n Γ)
  extend-tvar-comm Z Γ = refl 
  extend-tvar-comm (1+ n) Γ rewrite extend-tvar-comm n Γ = refl