open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-type-assignment-unicity

module debruijn.debruijn-elaboration-unicity where

  mutual

    elaboration-unicity-synth : ∀{Γ e τ1 τ2 d1 d2} →
      Γ ⊢ e ⇒ τ1 ~> d1 →
      Γ ⊢ e ⇒ τ2 ~> d2 →
      τ1 == τ2 × d1 == d2
    elaboration-unicity-synth ESConst ESConst = refl , refl
    elaboration-unicity-synth (ESVar x) (ESVar x₁) = context-unicity x x₁ , refl
    elaboration-unicity-synth (ESLam x syn1) (ESLam x₁ syn2) with elaboration-unicity-synth syn1 syn2 
    ... | refl , refl = refl , refl
    elaboration-unicity-synth (ESTLam syn1) (ESTLam syn2) with elaboration-unicity-synth syn1 syn2 
    ... | refl , refl = refl , refl
    elaboration-unicity-synth (ESAp x x₁ x₂ x₃) (ESAp x₄ x₅ x₆ x₇) rewrite synth-unicity x x₄ with ⊓-unicity x₁ x₅
    ... | refl with elaboration-unicity-ana x₂ x₆ | elaboration-unicity-ana x₃ x₇  
    ... | refl , refl | refl , refl = refl , refl
    elaboration-unicity-synth (ESTAp x x₁ x₂ x₃ refl) (ESTAp x₅ x₆ x₇ x₈ refl) rewrite synth-unicity x₁ x₆ with ⊓-unicity x₂ x₇ 
    ... | refl with elaboration-unicity-ana x₃ x₈ 
    ... | refl , refl = refl , refl
    elaboration-unicity-synth ESEHole ESEHole = refl , refl
    elaboration-unicity-synth (ESNEHole syn1) (ESNEHole syn2) with elaboration-unicity-synth syn1 syn2 
    ... | refl , refl = refl , refl
    elaboration-unicity-synth (ESAsc x x₁) (ESAsc x₂ x₃) with elaboration-unicity-ana x₁ x₃  
    ... | refl , refl = refl , refl

    elaboration-unicity-ana : ∀{Γ e τ τ1 τ2 d1 d2}  →
      Γ ⊢ e ⇐ τ ~> d1 :: τ1  → 
      Γ ⊢ e ⇐ τ ~> d2 :: τ2 →
      d1 == d2 × τ1 == τ2
    elaboration-unicity-ana (EALam x ana1) (EALam x₁ ana2) with ⊓-unicity x x₁
    ... | refl with elaboration-unicity-ana ana1 ana2 
    ... | refl , refl = refl , refl
    elaboration-unicity-ana (EATLam x ana1) (EATLam x₁ ana2) with ⊓-unicity x x₁
    ... | refl with elaboration-unicity-ana ana1 ana2 
    ... | refl , refl = refl , refl
    elaboration-unicity-ana (EATLam x ana1) (EASubsume (Subsumable neq) _ _) = abort (neq _ refl)
    elaboration-unicity-ana (EASubsume (Subsumable neq) _ _) (EATLam x ana2) = abort (neq _ refl)
    elaboration-unicity-ana (EASubsume x x₁ x₂) (EASubsume x₃ x₄ x₅) with elaboration-unicity-synth x₁ x₄ 
    ... | refl , refl rewrite ⊓-unicity x₂ x₅ = refl , refl