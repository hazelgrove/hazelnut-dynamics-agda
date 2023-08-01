open import Nat
open import Prelude
open import core
open typctx
open import contexts
open import disjointness
open import lemmas-well-formed
open import weakening


module hole-ctx-well-formed where 

  data _⊢_⊣_ : (Θ : typctx) → (d : ihexp) → (Δ : hctx) → Set where
    HCtxWfConst : ∀{ Θ Δ} → Θ ⊢ c ⊣ Δ
    HCtxWfVar : ∀{ Θ n Δ} → Θ ⊢ (X n) ⊣ Δ
    HCtxWfLam : ∀{ Θ d x τ Δ} → Θ ⊢ d ⊣ Δ → Θ ⊢ ·λ x [ τ ] d ⊣ Δ
    HCtxWfTLam : ∀{ Θ d Δ} → [ Θ newtyp] ⊢ d ⊣ Δ → Θ ⊢ ·Λ d ⊣ Δ
    HCtxWfAp : ∀{ Θ d1 d2 Δ} → Θ ⊢ d1 ⊣ Δ → Θ ⊢ d2 ⊣ Δ → Θ ⊢ d1 ∘ d2 ⊣ Δ
    HCtxWfTAp : ∀{ Θ τ d Δ} → Θ ⊢ d ⊣ Δ → Θ ⊢ d < τ > ⊣ Δ
    HCtxWfEHole : ∀{ Θ u σ Δ} → (∀{ Θ' Γ' τ} → (u , (Θ' , Γ' , τ)) ∈ Δ → Θ ⊢ τ wf) → Θ ⊢ ⦇-⦈⟨ u , σ ⟩ ⊣ Δ
    HCtxWfNEHole : ∀{ Θ u σ d Δ} → Θ ⊢ d ⊣ Δ → (∀{ Θ' Γ' τ} → (u , (Θ' , Γ' , τ)) ∈ Δ → Θ ⊢ τ wf) → Θ ⊢ ⦇⌜ d ⌟⦈⟨ u , σ ⟩ ⊣ Δ
    HCtxWfCast : ∀{ Θ τ1 τ2 d Δ} → Θ ⊢ d ⊣ Δ → Θ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ ⊣ Δ
    HCtxWfFailedCast : ∀{ Θ τ1 τ2 d Δ} → Θ ⊢ d ⊣ Δ → Θ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ⊣ Δ

  data _⊢_⊣_strict : (Θ : typctx) → (d : ihexp) → (Δ : hctx) → Set where
    HCtxWfStrictConst : ∀{ Θ} → Θ ⊢ c ⊣ ∅ strict
    HCtxWfStrictVar : ∀{ Θ n} → Θ ⊢ (X n) ⊣ ∅ strict
    HCtxWfStrictLam : ∀{ Θ d x τ Δ} → Θ ⊢ d ⊣ Δ strict → Θ ⊢ ·λ x [ τ ] d ⊣ Δ strict
    HCtxWfStrictTLam : ∀{ Θ d Δ} → [ Θ newtyp] ⊢ d ⊣ Δ strict → Θ ⊢ ·Λ d ⊣ Δ strict
    HCtxWfStrictAp : ∀{ Θ d1 d2 Δ1 Δ2} → Δ1 ## Δ2 → Θ ⊢ d1 ⊣ Δ1 strict → Θ ⊢ d2 ⊣ Δ2 strict → Θ ⊢ d1 ∘ d2 ⊣ Δ1 ∪ Δ2 strict
    HCtxWfStrictTAp : ∀{ Θ τ d Δ} → Θ ⊢ d ⊣ Δ strict → Θ ⊢ d < τ > ⊣ Δ strict
    HCtxWfStrictEHole : ∀{ Θ Γ τ u σ} → (Θ ⊢ τ wf) → Θ ⊢ ⦇-⦈⟨ u , σ ⟩ ⊣ ■ (u :: τ [ Θ , Γ ]) strict
    HCtxWfStrictNEHole : ∀{ Θ Γ τ u σ d Δ} → Δ ## (■ (u , Θ , Γ , τ)) → Θ ⊢ d ⊣ Δ strict → (Θ ⊢ τ wf) → Θ ⊢ ⦇⌜ d ⌟⦈⟨ u , σ ⟩ ⊣ Δ ,, (u :: τ [ Θ , Γ ]) strict
    HCtxWfStrictCast : ∀{ Θ τ1 τ2 d Δ} → Θ ⊢ d ⊣ Δ strict → Θ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ ⊣ Δ strict
    HCtxWfStrictFailedCast : ∀{ Θ τ1 τ2 d Δ} → Θ ⊢ d ⊣ Δ strict → Θ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ⊣ Δ strict
     
  singleton-lookup : ∀{ Θ Γ u Θ' Γ' τ τ'} → (u , Θ' , Γ' , τ') ∈ (■ (u :: τ [ Θ , Γ ])) → (τ == τ')
  singleton-lookup {u = u} {τ = τ} p with natEQ u u 
  singleton-lookup {u = u} {τ = τ} refl | Inl refl = refl
  ... | Inr absurd = abort (absurd refl)

  helper1 : ∀{ Θ Γ u Θ' Γ' τ} →  (u , Θ' , Γ' , τ) ∈ (■ (u :: ⦇-⦈ [ Θ , Γ ])) → Θ ⊢ τ wf
  helper1 p rewrite (sym (singleton-lookup p)) = WFHole 

  helper2 : ∀{ Θ Γ u τ} → dom (■ (u :: τ [ Θ , Γ ])) u
  helper2 {Θ = Θ} {Γ = Γ} {u = u} {τ = τ} with natEQ u u 
  ... | Inl refl = (( Θ , Γ , τ)) , refl
  ... | Inr absurd = abort (absurd refl)

  helper3 : ∀ {Θ Γ u Θ' Γ' τ τ'} → (u , Θ' , Γ' , τ) ∈ (■ (u :: τ' [ Θ , Γ ])) → Θ ⊢ τ' wf → Θ ⊢ τ wf
  helper3 p wf rewrite (singleton-lookup p) = wf

  helper4 : ∀ {Θ Γ u Θ' Γ' τ τ' Δ} → Δ ## (■ (u , Θ , Γ , τ)) → (u , Θ' , Γ' , τ') ∈ (Δ ,, (u :: τ [ Θ , Γ ])) → Θ ⊢ τ wf → Θ ⊢ τ' wf
  helper4 apt p wf = {!   !}

  -- apt-comm : ∀{Δ1 Δ2} → Δ1 ## Δ2 → Δ2 ## Δ1
  -- apt-comm = {!   !}

  hctx-wf-with-disjoint : ∀{ Θ d Δ1 Δ2} → Δ1 ## Δ2 → Θ ⊢ d ⊣ Δ1 strict → Θ ⊢ d ⊣ (Δ1 ∪ Δ2)
  hctx-wf-with-disjoint apt HCtxWfStrictConst = HCtxWfConst
  hctx-wf-with-disjoint apt HCtxWfStrictVar = HCtxWfVar
  hctx-wf-with-disjoint apt (HCtxWfStrictLam wf) = HCtxWfLam (hctx-wf-with-disjoint apt wf)
  hctx-wf-with-disjoint apt (HCtxWfStrictTLam wf) = HCtxWfTLam (hctx-wf-with-disjoint apt wf)
  hctx-wf-with-disjoint apt (HCtxWfStrictAp x wf wf₁) =  HCtxWfAp {! hctx-wf-with-disjoint ? ?  !} {! hctx-wf-with-disjoint ? ?  !}
  hctx-wf-with-disjoint apt (HCtxWfStrictTAp wf) = HCtxWfTAp (hctx-wf-with-disjoint apt wf)
  hctx-wf-with-disjoint apt (HCtxWfStrictEHole x) = {!   !}
  hctx-wf-with-disjoint apt (HCtxWfStrictNEHole apt2 wf x) = {!   !}
  hctx-wf-with-disjoint apt (HCtxWfStrictCast wf) = HCtxWfCast (hctx-wf-with-disjoint apt wf)
  hctx-wf-with-disjoint apt (HCtxWfStrictFailedCast wf) = HCtxWfFailedCast (hctx-wf-with-disjoint apt wf)
  
  hctx-wf-with-disjoint-flip : ∀{ Θ d Δ1 Δ2} → Δ1 ## Δ2 → Θ ⊢ d ⊣ Δ2 strict → Θ ⊢ d ⊣ (Δ1 ∪ Δ2)
  hctx-wf-with-disjoint-flip = {!   !}

  hctx-wf-strict-implies-plain : ∀{ Θ d Δ} →  Θ ⊢ d ⊣ Δ strict → Θ ⊢ d ⊣ Δ
  hctx-wf-strict-implies-plain HCtxWfStrictConst = HCtxWfConst
  hctx-wf-strict-implies-plain HCtxWfStrictVar = HCtxWfVar
  hctx-wf-strict-implies-plain (HCtxWfStrictLam wf) = HCtxWfLam (hctx-wf-strict-implies-plain wf)
  hctx-wf-strict-implies-plain (HCtxWfStrictTLam wf) = HCtxWfTLam (hctx-wf-strict-implies-plain wf)
  hctx-wf-strict-implies-plain (HCtxWfStrictAp x wf wf₁) = HCtxWfAp (hctx-wf-with-disjoint x wf) (hctx-wf-with-disjoint-flip x wf₁)
  hctx-wf-strict-implies-plain (HCtxWfStrictTAp wf) = HCtxWfTAp (hctx-wf-strict-implies-plain wf)
  hctx-wf-strict-implies-plain (HCtxWfStrictEHole x) = HCtxWfEHole (λ x₁ → helper3 x₁ x)
  hctx-wf-strict-implies-plain (HCtxWfStrictNEHole apt x x₁) = HCtxWfNEHole (hctx-wf-with-disjoint apt x) λ x₂ → helper4 apt x₂ x₁
  hctx-wf-strict-implies-plain (HCtxWfStrictCast wf) = HCtxWfCast (hctx-wf-strict-implies-plain wf)
  hctx-wf-strict-implies-plain (HCtxWfStrictFailedCast wf) = HCtxWfFailedCast (hctx-wf-strict-implies-plain wf)

  mutual 
    
    generate-hctx-wf-syn : ∀{ Θ Γ e τ d Δ} → Θ ⊢ Γ tctxwf → Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ → Θ ⊢ d ⊣ Δ strict
    generate-hctx-wf-syn ctxwf ESConst = HCtxWfStrictConst
    generate-hctx-wf-syn ctxwf (ESVar x) = HCtxWfStrictVar
    generate-hctx-wf-syn ctxwf (ESLam x x₁ wf) = HCtxWfStrictLam (generate-hctx-wf-syn (merge-tctx-wf ctxwf x₁ x) wf)
    generate-hctx-wf-syn ctxwf (ESTLam wf) = HCtxWfStrictTLam (generate-hctx-wf-syn (weaken-tctx-wf ctxwf) wf)
    generate-hctx-wf-syn ctxwf (ESAp x x₁ x₂ x₃ x₄ x₅) with (match-arr-wf (wf-synth ctxwf x₂) x₃) 
    ... | WFArr wf1 wf2 = HCtxWfStrictAp x₁ (HCtxWfStrictCast (generate-hctx-wf-ana ctxwf (WFArr wf1 wf2) x₄)) (HCtxWfStrictCast (generate-hctx-wf-ana ctxwf wf1 x₅))
    generate-hctx-wf-syn ctxwf (ESTAp x x₁ x₂ x₃ x₄) = HCtxWfStrictTAp (HCtxWfStrictCast (generate-hctx-wf-ana ctxwf (match-forall-wf (wf-synth ctxwf x₁) x₂) x₃))
    generate-hctx-wf-syn ctxwf ESEHole = HCtxWfStrictEHole WFHole
    generate-hctx-wf-syn ctxwf (ESNEHole x wf) = HCtxWfStrictNEHole x (generate-hctx-wf-syn ctxwf wf) WFHole
    generate-hctx-wf-syn ctxwf (ESAsc x x₁) = HCtxWfStrictCast (generate-hctx-wf-ana ctxwf x x₁)

    generate-hctx-wf-ana : ∀{ Θ Γ e τ τ' d Δ} → Θ ⊢ Γ tctxwf → Θ ⊢ τ wf → Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ → Θ ⊢ d ⊣ Δ strict
    generate-hctx-wf-ana ctxwf wft (EALam x x₁ wf) with match-arr-wf wft x₁ 
    ... | WFArr x₂ wf2 = HCtxWfStrictLam (generate-hctx-wf-ana (merge-tctx-wf ctxwf x₂ x) wf2 wf)
    generate-hctx-wf-ana ctxwf wft (EATLam x x₁ x₂ wf) with match-forall-wf wft x₂ 
    ... | WFForall wf2 =  HCtxWfStrictTLam (generate-hctx-wf-ana (weaken-tctx-wf ctxwf) wf2 wf)
    generate-hctx-wf-ana ctxwf wft (EASubsume x x₁ x₂ x₃) = generate-hctx-wf-syn ctxwf x₂
    generate-hctx-wf-ana ctxwf wft EAEHole = HCtxWfStrictEHole wft
    generate-hctx-wf-ana ctxwf wft (EANEHole x x₁) = HCtxWfStrictNEHole x (generate-hctx-wf-syn ctxwf x₁) wft