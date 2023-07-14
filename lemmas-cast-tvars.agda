open import Nat
open import Prelude
open import core
open typctx
open import contexts

data contains-tvar-cast : (d : ihexp) → Set where 
  CTVCast1 : ∀{d n τ} → contains-tvar-cast (d ⟨ (T n) ⇒ τ ⟩)
  CTVCast2 : ∀{d n τ} → contains-tvar-cast (d ⟨ τ ⇒ (T n) ⟩)
  CTVCastLam : ∀{d x τ} → contains-tvar-cast d → contains-tvar-cast (·λ x [ τ ] d)
  CTVCastTLam : ∀{d} → contains-tvar-cast d → contains-tvar-cast (·Λ d)
  CTVCastAp1 : ∀{d1 d2} →  contains-tvar-cast d1 → contains-tvar-cast (d1 ∘ d2)
  CTVCastAp2 : ∀{d1 d2} → contains-tvar-cast d2 → contains-tvar-cast (d1 ∘ d2)
  CTVCastTAp : ∀{d τ} → contains-tvar-cast d → contains-tvar-cast (d < τ >)
  CTVCastCast : ∀{d τ1 τ2} → contains-tvar-cast d → contains-tvar-cast (d ⟨ τ1 ⇒ τ2 ⟩)
  CTVCastFailedCast : ∀{d τ1 τ2} → contains-tvar-cast d → contains-tvar-cast (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

data is-tvar-cast : (d : ihexp) → Set where 
  TVCast1 : ∀{d n τ} → is-tvar-cast (d ⟨ (T n) ⇒ τ ⟩)
  TVCast2 : ∀{d n τ} → is-tvar-cast (d ⟨ τ ⇒ (T n) ⟩)

mutual 
  elab-wf-synth : ∀{Γ Θ e τ n d Δ} → 
                    Γ , Θ ⊢ e ⇒ τ ~> d ⊣ Δ → 
                    Θ ⊢ τ wf 
  elab-wf-synth ESConst = WFBase
  elab-wf-synth (ESVar x) = {!  !}
  elab-wf-synth (ESLam x x₁ wt) = {!   !}
  elab-wf-synth (ESTLam wt) = {!   !}
  elab-wf-synth (ESAp x x₁ x₂ x₃ x₄ x₅) = {!   !}
  elab-wf-synth (ESTAp x x₁ x₂ x₃ x₄) = {!   !}
  elab-wf-synth ESEHole = {!   !}
  elab-wf-synth (ESNEHole x wt) = {!   !}
  elab-wf-synth (ESAsc x x₁) = {!   !}

  elab-wf-ana : ∀{Γ Θ e τ1 τ2 n d Δ} → 
                    Γ , Θ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
                    Θ ⊢ τ2 wf 
  elab-wf-ana wt = {!   !}

mutual 
  no-tvar-elab-synth : ∀{e τ n d Δ} → 
                    ∅ , ~∅ ⊢ e ⇒ (T n) ~> d ⊣ Δ → 
                    ⊥
  no-tvar-elab-synth (ESAp x x₁ x₂ x₃ x₄ x₅) = {!   !}
  no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ x₄) with τ2 
  no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | b
  no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | ⦇-⦈
  no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | a ==> b
  no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | ·∀ a
  no-tvar-elab-synth (ESTAp {τ2 = τ2} (WFVar ()) x₁ x₂ x₃ x₄) | T Z
  no-tvar-elab-synth (ESAsc (WFVar ()) x₁)

  no-tvar-elab-ana : ∀{e τ n d Δ} → 
                      ∅ , ~∅ ⊢ e ⇐ τ ~> d :: (T n) ⊣ Δ → 
                      ⊥
  no-tvar-elab-ana (EASubsume x x₁ x₂ x₃) = {!   !}
  no-tvar-elab-ana EAEHole = {!   !}
  no-tvar-elab-ana (EANEHole x x₁) = {!   !}


mutual 
  no-tvar-cast-elab-synth : ∀{e τ d Δ} → 
                       ∅ , ~∅ ⊢ e ⇒ τ ~> d ⊣ Δ → 
                       is-tvar-cast d → 
                       ⊥
  no-tvar-cast-elab-synth (ESAsc x x₁) TVCast1 = no-tvar-elab-ana x₁
  no-tvar-cast-elab-synth (ESAsc (WFVar ()) x₁) TVCast2
                      
  no-tvar-cast-elab-ana : ∀{e τ1 τ2 d Δ} → 
                     ∅ , ~∅ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
                     is-tvar-cast d → 
                     ⊥
  no-tvar-cast-elab-ana (EASubsume x x₁ x₂ x₃) cast = no-tvar-cast-elab-synth x₂ cast

mutual 
  no-tvar-cast-synth : ∀{e τ d d' Δ} → 
                       ∅ , ~∅ ⊢ e ⇒ τ ~> d' ⊣ Δ → 
                       d' ↦* d → 
                       is-tvar-cast d → 
                       ⊥
  no-tvar-cast-synth wt steps cast = {!  !}
                      
  no-tvar-cast-ana : ∀{e τ1 τ2 d d' Δ} → 
                     ∅ , ~∅ ⊢ e ⇐ τ1 ~> d' :: τ2 ⊣ Δ → 
                     d' ↦* d → 
                     is-tvar-cast d → 
                     ⊥
  no-tvar-cast-ana wt steps cast = {!   !}


-- The following is false:
-- mutual 
--   no-tvar-cast-elab-synth : ∀{Γ e τ d Δ} → 
--                             Γ , ~∅ ⊢ e ⇒ τ ~> d ⊣ Δ → 
--                             contains-tvar-cast d → 
--                             ⊥
--   no-tvar-cast-elab-synth (ESLam x wt) (TVCastLam cast) = no-tvar-cast-elab-synth wt cast
--   no-tvar-cast-elab-synth (ESTLam wt) (TVCastTLam cast) = no-tvar-cast-elab-synth wt cast
--   no-tvar-cast-elab-synth (ESAp {τ1' = (T n)} x x₁ x₂ x₃ x₄ x₅) (TVCastAp1 TVCast1) = {!   !}
--   no-tvar-cast-elab-synth (ESAp x x₁ x₂ x₃ x₄ x₅) (TVCastAp1 (TVCastCast cast)) = no-tvar-cast-elab-ana x₄ cast
--   no-tvar-cast-elab-synth (ESAp x x₁ x₂ x₃ x₄ x₅) (TVCastAp2 TVCast1) = {!   !}
--   no-tvar-cast-elab-synth (ESAp x x₁ x₂ x₃ x₄ x₅) (TVCastAp2 TVCast2) = {!   !}
--   no-tvar-cast-elab-synth (ESAp x x₁ x₂ x₃ x₄ x₅) (TVCastAp2 (TVCastCast cast)) = no-tvar-cast-elab-ana x₅ cast
--   no-tvar-cast-elab-synth (ESTAp x x₁ x₂) (TVCastTAp TVCast1) = {!   !}
--   no-tvar-cast-elab-synth (ESTAp x x₁ x₂) (TVCastTAp (TVCastCast cast)) = no-tvar-cast-elab-ana x₂ cast
--   no-tvar-cast-elab-synth (ESAsc (EASubsume x x₁ x₂ x₃)) TVCast1 = {!   !}
--   no-tvar-cast-elab-synth (ESAsc EAEHole) TVCast1 = {!   !}
--   no-tvar-cast-elab-synth (ESAsc (EANEHole x x₁)) TVCast1 = {!   !}
--   no-tvar-cast-elab-synth (ESAsc (EASubsume x x₁ x₂ x₃)) TVCast2 = {!   !}
--   no-tvar-cast-elab-synth (ESAsc EAEHole) TVCast2 = {!   !}
--   no-tvar-cast-elab-synth (ESAsc (EANEHole x x₁)) TVCast2 = {!   !}
--   no-tvar-cast-elab-synth (ESAsc x) (TVCastCast cast) = no-tvar-cast-elab-ana x cast

--   no-tvar-cast-elab-ana : ∀{Γ e τ1 τ2 d Δ} → 
--                           Γ , ~∅ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
--                           contains-tvar-cast d → 
--                           ⊥
--   no-tvar-cast-elab-ana (EALam x x₁ wt) (TVCastLam cast) = no-tvar-cast-elab-ana wt cast
--   no-tvar-cast-elab-ana (EASubsume x x₁ x₂ x₃) cast = no-tvar-cast-elab-synth x₂ cast            