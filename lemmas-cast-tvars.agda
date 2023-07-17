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

merge-tctx-wf : ∀ {Θ Γ x x' τ τ'} → Θ ⊢ Γ tctxwf → Θ ⊢ τ wf → (x' , τ') ∈ (Γ ,, (x , τ)) → Θ ⊢ τ' wf -- Θ ⊢ (Γ ,, (x , τ)) tctxwf 
merge-tctx-wf a d e = {!   !}
-- merge-tctx-wf {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf mem with (natEQ x x')
-- merge-tctx-wf {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf mem | Inl refl with (ctxunicity {n = x} {t = τ} {t' = τ'} {!   !} {!   !})
-- merge-tctx-wf {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf mem | Inl refl | unic = {! twf ? !} 
-- merge-tctx-wf {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf mem | Inr absurd = {! ctxwf !} 

weakening-tctx-wf : ∀ {Θ Γ} → Θ ⊢ Γ tctxwf → [ Θ newtyp] ⊢ Γ tctxwf
weakening-tctx-wf h = {!   !}

weakening-t-wf : ∀ {Θ τ} → Θ ⊢ τ wf → [ Θ newtyp] ⊢ τ wf
weakening-t-wf h = {!   !}

wf-sub : ∀ {Θ τ1 τ2} → [ Θ newtyp] ⊢ τ1 wf → Θ ⊢ τ2 wf → Θ ⊢ Typ[ τ1 / Z ] τ2 wf
wf-sub a d = {!   !}

mutual 
  wf-synth : ∀{Θ Γ e τ} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ , Γ ⊢ e => τ → 
                    Θ ⊢ τ wf 
  wf-synth ctxwf SConst = WFBase
  wf-synth ctxwf (SAsc x x₁) = x
  wf-synth (CCtx wts) (SVar x) = wts x
  wf-synth ctxwf (SAp x wt MAHole x₂) = WFHole
  wf-synth ctxwf (SAp x wt MAArr x₂) = wf-synth-arr ctxwf wt
  wf-synth ctxwf SEHole = WFHole
  wf-synth ctxwf (SNEHole x wt) = WFHole
  wf-synth ctxwf (SLam x x₁ wt) = WFArr x₁ (wf-synth (CCtx (merge-tctx-wf ctxwf x₁)) wt)
  wf-synth ctxwf (STLam wt) = WFForall (wf-synth (weakening-tctx-wf ctxwf) wt)
  wf-synth ctxwf (STAp x wt MFHole eq) rewrite (sym eq) = WFHole
  wf-synth ctxwf (STAp x wt MFForall eq) rewrite (sym eq) = wf-sub (weakening-t-wf x) (wf-synth-forall ctxwf wt)

  wf-synth-arr : ∀{Θ Γ e τ τ'} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ , Γ ⊢ e => (τ' ==> τ) → 
                    Θ ⊢ τ wf 
  wf-synth-arr ctxwf (SAsc (WFArr _ wf) _) = wf
  wf-synth-arr (CCtx wfs) (SVar x) with (wfs x)
  ... | WFArr _ wf = wf
  wf-synth-arr ctxwf (SAp _ wf MAArr _) with wf-synth-arr ctxwf wf 
  ... | WFArr _ wf = wf
  wf-synth-arr ctxwf (SLam _ wf wt) = wf-synth (CCtx (merge-tctx-wf ctxwf wf)) wt
  wf-synth-arr ctxwf (STAp wf wt MFForall eq) with wf-synth-forall ctxwf wt
  ... | wf' with wf-sub (weakening-t-wf wf) wf'
  ... | wf rewrite eq with wf
  ... | WFArr _ wf = wf

  wf-synth-forall : ∀{Θ Γ e τ} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ , Γ ⊢ e => (·∀ τ) → 
                    Θ ⊢ τ wf 
  wf-synth-forall a d = {!   !}


mutual 

  elab-wf-synth : ∀{Θ Γ e τ d Δ} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ → 
                    Θ ⊢ τ wf 
  elab-wf-synth _ ESConst = WFBase
  elab-wf-synth (CCtx wts) (ESVar x) = wts x
  elab-wf-synth ctxwf (ESLam x₁ x₂ elab) = WFArr x₂ (elab-wf-synth (CCtx (merge-tctx-wf ctxwf x₂)) elab)
  elab-wf-synth ctxwf (ESTLam elab) = WFForall (elab-wf-synth (weakening-tctx-wf ctxwf) elab)
  elab-wf-synth ctxwf (ESAp _ _ _ MAHole _ _) = WFHole
  elab-wf-synth ctxwf (ESAp _ _ wt MAArr _ _) = wf-synth-arr ctxwf wt
  elab-wf-synth ctxwf (ESTAp wf wt _ _ eq) rewrite (sym eq) = wf-sub (weakening-t-wf wf) (wf-synth ctxwf wt)
  elab-wf-synth _ ESEHole = WFHole
  elab-wf-synth _ (ESNEHole _ _) = WFHole
  elab-wf-synth _ (ESAsc wf _) = wf

  elab-wf-ana : ∀{Γ Θ e τ1 τ2 d Δ} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ ⊢ τ1 wf → 
                    Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
                    Θ ⊢ τ2 wf 
  elab-wf-ana ctxwf wf1 (EALam x MAHole wt) = WFArr WFHole (elab-wf-ana (CCtx (merge-tctx-wf ctxwf WFHole)) wf1 wt)
  elab-wf-ana ctxwf (WFArr wf1 wf2) (EALam x MAArr wt) = WFArr wf1 (elab-wf-ana (CCtx (merge-tctx-wf ctxwf wf1)) wf2 wt)
  elab-wf-ana ctxwf wf1 (EASubsume x x₁ wt x₃) = elab-wf-synth ctxwf wt
  elab-wf-ana ctxwf wf1 EAEHole = wf1
  elab-wf-ana ctxwf wf1 (EANEHole x x₁) = wf1

-- mutual 
--   no-tvar-elab-synth : ∀{e τ n d Δ} → 
--                     ~∅ , ∅ ⊢ e ⇒ (T n) ~> d ⊣ Δ → 
--                     ⊥
--   no-tvar-elab-synth (ESAp x x₁ x₂ x₃ x₄ x₅) = {!   !}
--   no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ x₄) with τ2 
--   no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | b
--   no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | ⦇-⦈
--   no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | a ==> b
--   no-tvar-elab-synth (ESTAp {τ2 = τ2} x x₁ x₂ x₃ ()) | ·∀ a
--   no-tvar-elab-synth (ESTAp {τ2 = τ2} (WFVar ()) x₁ x₂ x₃ x₄) | T Z
--   no-tvar-elab-synth (ESAsc (WFVar ()) x₁)

--   no-tvar-elab-ana : ∀{e τ n d Δ} → 
--                       ~∅ , ∅ ⊢ e ⇐ τ ~> d :: (T n) ⊣ Δ → 
--                       ⊥
--   no-tvar-elab-ana (EASubsume x x₁ x₂ x₃) = {!   !}
--   no-tvar-elab-ana EAEHole = {!   !}
--   no-tvar-elab-ana (EANEHole x x₁) = {!   !}


-- mutual 
--   no-tvar-cast-elab-synth : ∀{e τ d Δ} → 
--                        ~∅ , ∅ ⊢ e ⇒ τ ~> d ⊣ Δ → 
--                        is-tvar-cast d → 
--                        ⊥
--   no-tvar-cast-elab-synth (ESAsc x x₁) TVCast1 = no-tvar-elab-ana x₁
--   no-tvar-cast-elab-synth (ESAsc (WFVar ()) x₁) TVCast2
                      
--   no-tvar-cast-elab-ana : ∀{e τ1 τ2 d Δ} → 
--                      ~∅ , ∅ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
--                      is-tvar-cast d → 
--                      ⊥
--   no-tvar-cast-elab-ana (EASubsume x x₁ x₂ x₃) cast = no-tvar-cast-elab-synth x₂ cast

-- mutual 
--   no-tvar-cast-synth : ∀{e τ d d' Δ} → 
--                        ~∅ , ∅ ⊢ e ⇒ τ ~> d' ⊣ Δ → 
--                        d' ↦* d → 
--                        is-tvar-cast d → 
--                        ⊥
--   no-tvar-cast-synth wt steps cast = {!  !}
                      
--   no-tvar-cast-ana : ∀{e τ1 τ2 d d' Δ} → 
--                      ~∅ , ∅ ⊢ e ⇐ τ1 ~> d' :: τ2 ⊣ Δ → 
--                      d' ↦* d → 
--                      is-tvar-cast d → 
--                      ⊥
--   no-tvar-cast-ana wt steps cast = {!   !}


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
 