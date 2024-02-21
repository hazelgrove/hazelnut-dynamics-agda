open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core

module debruijn.debruijn-elaboration-unicity where

  mutual
    elabortation-unicity-compatible : ∀{Γ e τ τ1 τ2 d1 d2 Δ1 Δ2 Θ} →
      ((u : Nat) → e ≠ ⦇-⦈) →
      ((e' : hexp) (u : Nat) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
      Θ , Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ1 →
      Θ , Γ ⊢ e ⇐ τ ~> d2 :: τ2 ⊣ Δ2 → 
      τ1 == τ2 × d1 == d2 × Δ1 == Δ2