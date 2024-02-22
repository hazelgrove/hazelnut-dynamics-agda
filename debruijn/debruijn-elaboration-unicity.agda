open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-type-assignment-unicity

module debruijn.debruijn-elaboration-unicity where

  mutual
    elabortation-unicity-compatible : ∀{Γ e τ τ1 τ2 d1 d2} →
      (e ≠ ⦇-⦈) →
      ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈) →
      Γ ⊢ e ⇒ τ1 ~> d1 →
      Γ ⊢ e ⇐ τ ~> d2 :: τ2 → 
      τ1 == τ2 × d1 == d2
    elabortation-unicity-compatible neq _ syn EAEHole = abort (neq refl)
    elabortation-unicity-compatible _ neq syn (EANEHole x) = abort (neq _ refl)
    elabortation-unicity-compatible _ _ (ESTLam neq1 neq2 syn) (EATLam _ ana) with elabortation-unicity-compatible neq1 neq2 syn ana 
    ... | refl , refl = refl , refl
    elabortation-unicity-compatible _ _ syn (EASubsume x x₁ x₂) = {!   !}

    elaboration-unicity-synth : ∀{Γ e τ1 τ2 d1 d2} →
      Γ ⊢ e ⇒ τ1 ~> d1 →
      Γ ⊢ e ⇒ τ2 ~> d2 →
      τ1 == τ2 × d1 == d2
    elaboration-unicity-synth ESConst ESConst = refl , refl
    elaboration-unicity-synth (ESVar x) (ESVar x₁) = context-unicity x x₁ , refl
    elaboration-unicity-synth (ESLam x syn1) (ESLam x₁ syn2) with elaboration-unicity-synth syn1 syn2 
    ... | refl , refl = refl , refl
    elaboration-unicity-synth (ESTLam x x₁ syn1) (ESTLam x₂ x₃ syn2) with elaboration-unicity-synth syn1 syn2 
    ... | refl , refl = refl , refl
    elaboration-unicity-synth (ESAp x x₁ x₂ x₃) (ESAp x₄ x₅ x₆ x₇) rewrite synth-unicity x x₄ with ⊓-unicity x₁ x₅
    ... | refl with elaboration-unicity-ana x₂ x₆ | elaboration-unicity-ana x₃ x₇  
    ... | refl , refl | refl , refl = refl , refl
    elaboration-unicity-synth (ESTAp x x₁ x₂ x₃ refl) (ESTAp x₅ x₆ x₇ x₈ refl) = {!   !}
    elaboration-unicity-synth ESEHole ESEHole = refl , refl
    elaboration-unicity-synth (ESNEHole syn1) (ESNEHole syn2) with elaboration-unicity-synth syn1 syn2 
    ... | refl , refl = refl , refl
    elaboration-unicity-synth (ESAsc x x₁) (ESAsc x₂ x₃) with elaboration-unicity-ana x₁ x₃  
    ... | refl , refl = refl , refl

    elaboration-unicity-ana : ∀{Γ e τ τ1 τ2 d1 d2}  →
      Γ ⊢ e ⇐ τ ~> d1 :: τ1  → 
      Γ ⊢ e ⇐ τ ~> d2 :: τ2 →
      d1 == d2 × τ1 == τ2
    elaboration-unicity-ana ana1 ana2 = {!   !}