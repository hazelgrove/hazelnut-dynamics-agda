open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-meet

module debruijn.debruijn-elaboration-generality where

  mutual 
    
    elaboration-generality-synth : ∀{Γ e τ d} →
      Γ ⊢ e ⇒ τ ~> d →
      Γ ⊢ e => τ
    elaboration-generality-synth ESConst = SConst
    elaboration-generality-synth (ESVar x) = SVar x
    elaboration-generality-synth (ESLam x syn) = SLam x (elaboration-generality-synth syn)
    elaboration-generality-synth (ESTLam syn) = STLam (elaboration-generality-synth syn)
    elaboration-generality-synth (ESAp x x₁ x₂ ana) = SAp x x₁ (elaboration-generality-ana ana)
    elaboration-generality-synth (ESTAp x x₁ x₂ x₃ x₄) = STAp x x₁ x₂ x₄
    elaboration-generality-synth ESEHole = SEHole
    elaboration-generality-synth (ESNEHole syn) = SNEHole (elaboration-generality-synth syn)
    elaboration-generality-synth (ESAsc x ana) = SAsc x (elaboration-generality-ana ana)

    elaboration-generality-ana : ∀{Γ e τ τ' d} →
      Γ ⊢ e ⇐ τ ~> d :: τ' →
      Γ ⊢ e <= τ
    elaboration-generality-ana (EALam x ana) = ALam x (elaboration-generality-ana ana)
    elaboration-generality-ana (EATLam x ana) = ATLam x (elaboration-generality-ana ana)
    elaboration-generality-ana (EASubsume x x₁ x₂) = ASubsume (elaboration-generality-synth x₁) (⊓-consist x₂)