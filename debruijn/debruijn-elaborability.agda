open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-type-assignment-unicity

module debruijn.debruijn-elaborability where

  mutual
    elaborability-synth : ∀{Γ e τ} →
      Γ ⊢ e => τ →
      Σ[ d ∈ ihexp ] (Γ ⊢ e ⇒ τ ~> d)
    elaborability-synth SConst = c , ESConst
    elaborability-synth (SAsc wf ana) with elaborability-ana ana 
    ... | d , τ , ana' = d ⟨ τ ⇒ _ ⟩ , ESAsc wf ana'
    elaborability-synth (SVar x) = X _ , ESVar x
    elaborability-synth (SAp syn x ana) with elaborability-synth syn | elaborability-ana (ASubsume syn (⊑t-consist (π1 (⊓-lb x)))) | elaborability-ana ana
    ... | d1 , syn' | d2 , τ1 , ana1 | d3 , τ2 , ana2 = ((d2 ⟨ τ1 ⇒ _ ⟩) ∘ (d3 ⟨ _ ⇒ _ ⟩)) , (ESAp syn x ana1 ana2)
    elaborability-synth SEHole = ⦇-⦈ , ESEHole
    elaborability-synth (SNEHole syn) with elaborability-synth syn 
    ... | d , elab = ⦇⌜ d ⌟⦈ , ESNEHole elab
    elaborability-synth (SLam x syn) with elaborability-synth syn 
    ... | d , elab = (·λ[ _ ] d) , ESLam x elab
    elaborability-synth (STLam syn) with elaborability-synth syn 
    ... | d , elab = ·Λ d , ESTLam elab
    elaborability-synth (STAp x syn x₁ refl) with elaborability-ana (ASubsume syn (⊑t-consist (π1 (⊓-lb x₁)))) 
    ... | d , τ , elab = ((d ⟨ τ ⇒ ·∀ _ ⟩) < _ >) , (ESTAp x syn x₁ elab refl)

    is-tlam : (e : hexp) → ((e' : hexp) → e ≠ ·Λ e') + ( Σ[ e' ∈ hexp ] (e == ·Λ e') )
    is-tlam c = Inl (λ x ())
    is-tlam (e ·: x) = Inl (λ x ())
    is-tlam (X x) = Inl (λ x ())
    is-tlam (·λ e) = Inl (λ x ())
    is-tlam (·λ[ x ] e) = Inl (λ x ())
    is-tlam (·Λ e) = Inr (e , refl)
    is-tlam ⦇-⦈ = Inl (λ x ())
    is-tlam ⦇⌜ e ⌟⦈ = Inl (λ x ())
    is-tlam (e ∘ e₁) = Inl (λ x ())
    is-tlam (e < x >) = Inl (λ x ())

    elaborability-ana : ∀{Γ e τ} →
      Γ ⊢ e <= τ →
      Σ[ d ∈ ihexp ] Σ[ τ' ∈ htyp ] (Γ ⊢ e ⇐ τ ~> d :: τ')
    elaborability-ana (ALam x ana) with elaborability-ana ana
    ... | d , τ , elab = (·λ[ _ ] d) , _ ==> τ , EALam x elab
    elaborability-ana (ATLam x ana) with elaborability-ana ana
    ... | d , τ , elab =  ·Λ d , ·∀ τ , EATLam x elab 
    elaborability-ana {e = e} (ASubsume syn meet) with is-tlam e 
    elaborability-ana {e = e} (ASubsume syn meet) | Inl neq with elaborability-synth syn | ⊓-ability meet
    elaborability-ana {e = e} (ASubsume syn meet) | Inl neq | d , elab | τ , meet' = _ , _ , (EASubsume (Subsumable neq) elab meet')
    elaborability-ana {e = .(·Λ e')} (ASubsume (STLam syn) ConsistHole2) | Inr (e' , refl) with elaborability-ana (ASubsume syn ConsistHole2)
    elaborability-ana {e = .(·Λ e')} (ASubsume (STLam syn) ConsistHole2) | Inr (e' , refl) | d , τ , elab  = ·Λ d , ·∀ τ , EATLam MeetHoleL elab
    elaborability-ana {e = .(·Λ e')} (ASubsume (STLam syn) (ConsistForall con)) | Inr (e' , refl) with elaborability-ana (ASubsume syn con)
    elaborability-ana {e = .(·Λ e')} (ASubsume (STLam syn) (ConsistForall con)) | Inr (e' , refl) | d , τ , elab  = ·Λ d , ·∀ τ , EATLam (MeetForall MeetHoleR) elab