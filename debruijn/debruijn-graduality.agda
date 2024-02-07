open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-typed-elaboration
open import debruijn.debruijn-type-assignment-unicity

module debruijn.debruijn-graduality where

  mutual

    graduality-ana : 
      ∀{τ τ' e e' Θ Γ Γ'} →
      (Γ ⊑c Γ') →
      (τ ⊑t τ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e <= τ) →
      (Θ , Γ' ⊢ e' <= τ') 

    graduality-ana precc prect PEHole ana = ASubsume SEHole ConsistHole1
    graduality-ana precc prect prec (ASubsume syn consist) with graduality-syn precc prec syn 
    ... | τ' , syn' , prect' = ASubsume syn' (⊑t-consist-left (⊑t-consist-right consist prect') prect)
    graduality-ana precc prect (PLam1 prec) (ALam meet ana) with ⊑t-⊓ prect (⊑t-refl _) meet 
    ... | .(_ ==> _) , meet' , PTArr prect1 prect2 = ALam meet' (graduality-ana (PCExtend prect1 precc) prect2 prec ana)
    graduality-ana precc prect (PTLam prec) (ATLam meet ana) with ⊑t-⊓ prect (⊑t-refl _) meet
    ... | .(·∀ _) , meet' , PTForall prect' = ATLam  meet' (graduality-ana precc prect' prec ana)
    
    graduality-syn : 
      ∀{e e' Θ Γ Γ' τ} →
      (Γ ⊑c Γ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e => τ) →
      Σ[ τ' ∈ htyp ] ((Θ , Γ' ⊢ e' => τ') × (τ ⊑t τ'))
    graduality-syn precc PEHole syn = ⦇-⦈ , SEHole , PTHole
    graduality-syn precc PConst SConst = b , SConst , PTBase
    graduality-syn precc PVar (SVar inctx) with ⊑c-var inctx precc
    ... | τ' , inctx' , prect = τ' , SVar inctx' , prect
    graduality-syn {e' = e' ·: τ'} precc (PAsc prec prect) (SAsc wf ana) 
      = τ' , SAsc (wf-⊑t wf prect) (graduality-ana precc prect prec ana) , prect
    graduality-syn precc (PLam2 prec prect) (SLam wf syn) with graduality-syn (PCExtend prect precc) prec syn 
    ... | τ' , syn' , prect' = _ , SLam (wf-⊑t wf prect) syn' , PTArr prect prect'
    graduality-syn precc (PTLam prec) (STLam syn) with graduality-syn precc prec syn 
    ... | τ' , syn' , prect' = _ , STLam syn' , PTForall prect'
    graduality-syn precc (PNEHole prec) (SNEHole syn) with graduality-syn precc prec syn 
    ... | τ' , syn' , prect' = _ , SNEHole syn' , PTHole
    graduality-syn precc (PAp prec1 prec2) (SAp syn meet ana) with graduality-syn precc prec1 syn
    ... | τ' , wt' , prect with ⊑t-⊓ prect (⊑t-refl _) meet 
    ... | .(_ ==> _) , meet' , PTArr prect' prect'' = _ ,  SAp wt' meet' (graduality-ana precc prect' prec2 ana) , prect''
    graduality-syn precc (PTAp {τ2 = τ2} prec prect) (STAp wf syn meet subst) rewrite (sym subst) with graduality-syn precc prec syn 
    ... | τ' , syn' , prect' with ⊑t-⊓ prect' (⊑t-refl _) meet
    ... | .(·∀ _) , meet' , PTForall prect' = _ , STAp (wf-⊑t wf prect) syn' meet' refl , ⊑t-TTsub prect prect'

  graduality1 : 
    ∀{e e' τ} →     
    (e ⊑ e') →
    (Z , ∅ ⊢ e => τ) → 
    Σ[ τ' ∈ htyp ] ((Z , ∅ ⊢ e' => τ') × (τ ⊑t τ'))
  graduality1 prec wt = graduality-syn PCEmpty prec wt

  -- graduality-elab-ana-fun : 
  --   ∀{e e' τ1 τ2 τ1' τ2' d d' Γ Γ' Θ} →     
  --   (Γ ⊑c Γ') →
  --   (τ1 ⊑t τ1') →
  --   (e ⊑ e') →
  --   (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
  --   (Θ , Γ' ⊢ e' ⇐ τ1' ~> d' :: τ2') →
  --   ((Θ , Γ , Γ' ⊢ d ⊑i d') × (τ2 ⊑t τ2'))
  -- graduality-elab-ana-fun precc prect prec ana (EALam x ana') = {!   !}
  -- graduality-elab-ana-fun precc prect prec ana (EATLam x x₁ x₂ ana') = {!   !}
  -- graduality-elab-ana-fun precc prect prec ana (EASubsume x x₁ x₂ x₃) = {!   !}
  -- graduality-elab-ana-fun precc prect prec ana EAEHole = PIEHole , {!   !}
  -- graduality-elab-ana-fun precc prect prec ana (EANEHole x) = {!   !}

  -- graduality-elab-syn-fun : 
  --   ∀{e e' τ τ' d d' Γ Γ' Θ} →     
  --   (Γ ⊑c Γ') →
  --   (e ⊑ e') →
  --   (Θ , Γ ⊢ e ⇒ τ ~> d) →
  --   (Θ , Γ' ⊢ e' ⇒ τ' ~> d') →
  --   ((Θ , Γ , Γ' ⊢ d ⊑i d') × (τ ⊑t τ'))
  -- graduality-elab-syn-fun = {!   !}

  hole-or-not : (e : hexp) → ((e == ⦇-⦈) + ( Σ[ e' ∈ hexp ] (e == ⦇⌜ e' ⌟⦈) ) + ((e ≠ ⦇-⦈) × ((e' : hexp) → e ≠ ⦇⌜ e' ⌟⦈)))
  hole-or-not c = Inr (Inr ((λ ()) , (λ x ())))
  hole-or-not (e ·: x) = Inr (Inr ((λ ()) , (λ x ())))
  hole-or-not (X x) = Inr (Inr ((λ ()) , (λ x ())))
  hole-or-not (·λ e) = Inr (Inr ((λ ()) , (λ x ())))
  hole-or-not (·λ[ x ] e) = Inr (Inr ((λ ()) , (λ x ())))
  hole-or-not (·Λ e) = Inr (Inr ((λ ()) , (λ x ())))
  hole-or-not ⦇-⦈ = Inl refl
  hole-or-not ⦇⌜ e ⌟⦈ = Inr (Inl (e , refl))
  hole-or-not (e ∘ e₁) = Inr (Inr ((λ ()) , (λ x ())))
  hole-or-not (e < x >) = Inr (Inr ((λ ()) , (λ x ())))

  -- ⊑i-trans : ∀{Θ Γ1 Γ2 Γ3 d1 d2 d3} → Γ1 ⊑c Γ2 → Γ2 ⊑c Γ3 → Θ , Γ1 , Γ2 ⊢ d1 ⊑i d2 → Θ , Γ2 , Γ3 ⊢ d2 ⊑i d3 → Θ , Γ1 , Γ3 ⊢ d1 ⊑i d3
  -- ⊑i-trans precc1 precc2 prec1 PIEHole = PIEHole
  -- ⊑i-trans precc1 precc2 (PIBlame TAConst PTBase) PIConst = PIBlame TAConst PTBase
  -- ⊑i-trans precc1 precc2 (PIBlame (TAVar inctx) prec) PIVar with ⊑c-var inctx precc2 
  -- ... | τ , inctx' , prec' = PIBlame (TAVar inctx') (⊑t-trans prec prec')
  -- ⊑i-trans precc1 precc2 (PIBlame (TALam x₁ wt) prec1) (PILam prec2 x) = PIBlame (TALam (wf-⊑t x₁ x) {!   !}) {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PITLam prec2) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PINEHole prec2 x) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIAp prec2 prec3) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PITAp prec2 x) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PICast prec2 x x₁) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIFailedCast prec2 x x₁) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIRemoveCast prec2 x x₁ x₂) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIAddCast prec2 x x₁ x₂) = {!   !}
  -- ⊑i-trans precc1 precc2 (PIBlame wt prec1) (PIBlame x x₁) = {!   !} 
  -- ⊑i-trans precc1 precc2 PIConst PIConst = {!   !}
  -- ⊑i-trans precc1 precc2 (PIRemoveCast prec1 x x₁ x₂) PIConst = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 PIVar = {!   !} 
  -- ⊑i-trans precc1 precc2 (PILam prec1 prec2) (PILam prec3 prec4) = PILam (⊑i-trans (PCExtend prec2 precc1) (PCExtend prec4 precc2) prec1 prec3) (⊑t-trans prec2 prec4)
  -- ⊑i-trans precc1 precc2 (PIRemoveCast prec1 x₁ x₂ x₃) (PILam prec2 x) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PITLam prec2) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PINEHole prec2 x) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PIAp prec2 prec3) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PITAp prec2 x) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PICast prec2 x x₁) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PIFailedCast prec2 x x₁) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PIRemoveCast prec2 x x₁ x₂) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PIAddCast prec2 x x₁ x₂) = {!   !}
  -- ⊑i-trans precc1 precc2 prec1 (PIBlame x x₁) = {!   !}

  mutual 
      
    -- graduality-elab-ana : 
    --   ∀{e e' τ1 τ2 τ1' Γ Γ' Θ d} →     
    --   (Θ ⊢ Γ ctxwf) → 
    --   (Θ ⊢ τ1 wf) → 
    --   (Γ ⊑c Γ') →
    --   (τ1 ⊑t τ1') →
    --   (e ⊑ e') →
    --   (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
    --   Σ[ d' ∈ ihexp ] Σ[ τ2' ∈ htyp ] ((Θ , Γ' ⊢ e' ⇐ τ1' ~> d' :: τ2') × (Θ , Γ , Γ' ⊢ d ⊑i d') × (τ2 ⊑t τ2'))
    -- graduality-elab-ana {e' = e'} ctxwf wf precc prect prec (EASubsume neq1 neq2 syn meet) with hole-or-not e' 
    -- graduality-elab-ana ctxwf wf precc prect prec (EASubsume neq1 neq2 syn meet) | Inl refl = _ , _ , EAEHole , PIEHole , ⊑t-trans (π1 (⊓-lb meet)) prect
    -- graduality-elab-ana ctxwf wf precc prect prec (EASubsume neq1 neq2 syn meet) | Inr (Inl (e' , refl)) with graduality-elab-syn ctxwf precc prec syn | ⊓-lb meet 
    -- graduality-elab-ana ctxwf wf precc prect prec (EASubsume neq1 neq2 (ESNEHole syn) meet) | Inr (Inl (e' , refl)) | τ' , d' , syn' , prec1 , prec2 | prect' , _
    --   = abort (neq2 _ refl)
    -- graduality-elab-ana ctxwf wf precc prect prec (EASubsume neq1 neq2 syn meet) | Inr (Inr (neq3 , neq4)) with graduality-elab-syn ctxwf precc prec syn | ⊓-lb meet
    -- graduality-elab-ana ctxwf wf precc prect prec (EASubsume neq1 neq2 syn meet) | Inr (Inr (neq3 , neq4)) | τ2' , d' , syn' , prect1 , prec' | prect2 , prect3 with ⊑t-⊓ prect prect1 meet
    -- ... | τ3' , meet' , prect4  = _ , _ , EASubsume neq3 neq4 syn' meet' , PICast prec' prect1 prect4 , prect4
    -- graduality-elab-ana ctxwf wf precc prect PEHole ana = _ , _ , EAEHole , PIEHole , ⊑t-trans (⊑t-ana ana) prect
    -- graduality-elab-ana ctxwf wf precc prect (PLam1 prec) (EALam meet ana) with ⊑t-⊓ prect (⊑t-refl _) meet | wf-⊓ meet wf (WFArr WFHole WFHole)
    -- ... | (τ1' ==> τ2') , prect1 , PTArr prect2 prect3 | WFArr wf1 wf2 with graduality-elab-ana (CtxWFExtend wf1 ctxwf) wf2 (PCExtend prect2 precc) prect3 prec ana 
    -- ... | d' , τ' , ana' , prec' , prect' = _ , _ , EALam prect1 ana' , PILam prec' prect2 , PTArr prect2 prect'

    -- graduality-elab-ana ctxwf wf precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) with ⊑t-⊓ prect (⊑t-refl _) meet | wf-⊓ meet wf (WFForall WFHole)
    -- graduality-elab-ana ctxwf wf precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) | (·∀ τ') , meet' , PTForall prect1 | WFForall wf' with graduality-elab-ana (weakening-ctx ctxwf) wf' precc prect1 prec ana
    -- graduality-elab-ana {e' = ·Λ e'} ctxwf wf precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) | (·∀ τ') , meet' , PTForall prect1 | wf' | thing , thing2 , ana' , prec' , prect2 with hole-or-not e'
    -- -- graduality-elab-ana precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) | .⦇-⦈ , MFHole , prect1 | thing , thing2 , ana' , prec' , prect2 | Inl refl =  _ , _ , EASubsume (λ ()) (λ e' ()) (ESTLam ESEHole) MeetHoleL , PIAddCast (PITLam PIEHole) (TATLam {!   !}) {!   !} {!   !} , PTForall PTHole 
    -- graduality-elab-ana ctxwf wf precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) | τ' , meet2 , prect1 | wf' | thing , thing2 , ana' , prec' , prect2 | Inl refl = 
    --   {!   !} --_ , _ , EASubsume (λ ()) (λ e' ()) (ESTLam ESEHole) {!   !} , {!   !} , {!   !}
    -- graduality-elab-ana ctxwf wf precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) | _ , meet2 , PTForall _ | wf' | _ , thing2 , EASubsume x x₁ x₂ x₃ , prec' , prect2 | Inr (Inl (e' , refl)) = 
    --   {!   !}
    -- graduality-elab-ana ctxwf wf precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) | ·∀ _ , meet2 , PTForall _ | WFForall wf' | _ , _ , EANEHole x , PINEHole prec' x₁ , prect2 | Inr (Inl (e' , refl)) =
    --   _ , _ , (EASubsume (λ ()) (λ e' ()) (ESTLam (ESNEHole x)) meet2) , PIAddCast (PITLam (PINEHole prec' PTHole)) (TATLam (typed-elaboration-ana (weakening-ctx ctxwf) wf' ana)) (PTForall PTHole) (PTForall prect2) , PTForall prect2

    -- graduality-elab-ana ctxwf wf precc prect (PTLam prec) (EATLam neq1 neq2 meet ana) | ·∀ _ , meet2 , PTForall _ | WFForall wf' | _ , _ , EANEHole x , PIRemoveCast prec' TANEHole x₂ x₃ , prect2 | Inr (Inl (e' , refl)) = 
    --   _ , _ , (EASubsume (λ ()) (λ e' ()) (ESTLam (ESNEHole x)) meet2) , PIAddCast (PITLam (PIRemoveCast {!   !} {!   !} {!   !} {!   !})) (TATLam (typed-elaboration-ana (weakening-ctx ctxwf) wf' ana)) (PTForall PTHole) (PTForall prect2) , PTForall prect2
    -- ... | Inr (Inr (neq3 , neq4)) = _ , _ , EATLam neq3 neq4 meet' ana' , PITLam prec' , PTForall prect2
    
    -- graduality-elab-ana ctxwf wf precc prect (PNEHole prec) (EANEHole syn) with graduality-elab-syn {!   !} precc prec syn 
    -- ... | τ' , d' , syn' , prect' , prec' = _ , _ , EANEHole syn' , PINEHole prec' prect , prect

    -- graduality-elab-syn : 
    --   ∀{e e' Γ Γ' Θ τ d} →     
    --   (Θ ⊢ Γ ctxwf) → 
    --   (Γ ⊑c Γ') →
    --   (e ⊑ e') →
    --   (Θ , Γ ⊢ e ⇒ τ ~> d) →
    --   Σ[ τ' ∈ htyp ] Σ[ d' ∈ ihexp ] ((Θ , Γ' ⊢ e' ⇒ τ' ~> d') × (τ ⊑t τ') × (Θ , Γ , Γ' ⊢ d ⊑i d'))
    -- graduality-elab-syn ctxwf precc PEHole elab = ⦇-⦈ , ⦇-⦈⟨ ⦇-⦈ ⟩ , ESEHole , PTHole , PIEHole
    -- graduality-elab-syn ctxwf precc PConst ESConst = b , c , ESConst , PTBase , PIConst
    -- graduality-elab-syn ctxwf precc PVar (ESVar inctx) with ⊑c-var inctx precc
    -- ... | τ' , inctx' , prect = _ , _ , ESVar inctx' , prect , PIVar
    -- graduality-elab-syn ctxwf precc (PAsc prec x) (ESAsc wf ana) with graduality-elab-ana ctxwf wf precc x prec ana 
    -- ... | d' , τ2' , ana' , prec' , prect = _ , _ , ESAsc (wf-⊑t wf x) ana' , x , PICast prec' prect x
    -- graduality-elab-syn ctxwf precc (PLam2 prec x) (ESLam wf elab) with graduality-elab-syn (CtxWFExtend wf ctxwf) (PCExtend x precc) prec elab 
    -- ... | τ' , d' , elab' , prect , prec' = _ , _ , ESLam (wf-⊑t wf x) elab' , PTArr x prect , PILam prec' x
    -- graduality-elab-syn ctxwf precc (PTLam prec) (ESTLam elab) with graduality-elab-syn (weakening-ctx ctxwf) precc prec elab 
    -- ... | τ' , d' , elab' , prect , prec' = _ , _ , ESTLam elab' , PTForall prect , PITLam prec'
    -- graduality-elab-syn ctxwf precc (PNEHole prec) (ESNEHole elab) with graduality-elab-syn ctxwf precc prec elab 
    -- ... | τ' , d' , elab' , prect , prec' = _ , _ , ESNEHole elab' , PTHole , PINEHole prec' PTHole
    -- graduality-elab-syn ctxwf precc (PAp prec1 prec2) (ESAp syn meet ana1 ana2) with graduality-syn precc prec1 syn 
    -- ... | τ1' , syn' , prec1' with ⊑t-⊓ prec1' (⊑t-refl _) meet | wf-⊓ meet (wf-syn ctxwf syn) (WFArr WFHole WFHole)
    -- ... | (_ ==> _) , meet' , PTArr prec3 prec4 | WFArr wf1 wf2 with graduality-elab-ana ctxwf (WFArr wf1 wf2) precc (PTArr prec3 prec4) prec1 ana1 
    -- ... | d1' , τ1''' , ana1' , prec5 , prec6 with graduality-elab-ana ctxwf wf1 precc prec3 prec2 ana2 
    -- ... | d2' , τ2''' , ana2' , prec7 , prec8 = 
    --   _ , _ , (ESAp syn' meet' ana1' ana2') , prec4 , PIAp (PICast prec5 prec6 (PTArr prec3 prec4)) (PICast prec7 prec8 prec3)
    -- graduality-elab-syn ctxwf precc (PTAp prec prect) (ESTAp wf syn meet ana sub) with graduality-syn precc prec syn 
    -- ... | τ4' , syn' , prec1 with ⊑t-⊓ prec1 (⊑t-refl _) meet
    -- ... | (·∀ τ4'') , meet' , PTForall prec2 with graduality-elab-ana ctxwf (wf-⊓ meet (wf-syn ctxwf syn) (WFForall WFHole)) precc (PTForall prec2) prec ana 
    -- ... | d' , τ2'' , ana' , prec3 , prec4 rewrite (sym sub) with ⊑t-⊓-fun prec1 (PTForall PTHole) meet meet' 
    -- ... | PTForall prec5 = _ , _ , ESTAp (wf-⊑t wf prect) syn' meet' ana' refl , 
    --   ⊑t-TTsub prect prec5 , PITAp (PICast prec3 prec4 (PTForall prec2)) prect
   
    graduality-type-assign : 
      ∀{d d' Γ Γ' Θ τ} →     
      (Θ ⊢ Γ ctxwf) → 
      (Γ ⊑c Γ') →
      (Θ , Γ , Γ' ⊢ d ⊑i d') →
      (Θ , Γ ⊢ d :: τ) →
      Σ[ τ' ∈ htyp ] ((Θ , Γ' ⊢ d' :: τ') × (τ ⊑t τ'))
    graduality-type-assign ctxwf precc PIConst TAConst = b , TAConst , PTBase 
    graduality-type-assign ctxwf precc PIVar (TAVar inctx) with ⊑c-var inctx precc 
    ... | τ , inctx' , prec = τ , TAVar inctx' , prec
    graduality-type-assign ctxwf precc (PIEHole wt1 prec) wt2 rewrite type-assignment-unicity wt1 wt2 = _ , TAEHole , prec
    graduality-type-assign ctxwf precc (PILam prec x) (TALam x₁ wt) = {!   !}
    graduality-type-assign ctxwf precc (PITLam prec) (TATLam wt) = {!   !}
    graduality-type-assign ctxwf precc (PINEHole prec x) TANEHole = {!   !}
    graduality-type-assign ctxwf precc (PIAp prec prec₁) (TAAp wt wt₁) = {!   !}
    graduality-type-assign ctxwf precc (PITAp prec x) (TATAp x₁ wt x₂) = {!   !}
    graduality-type-assign ctxwf precc (PICast prec x x₁) (TACast wt x₂ x₃) = {!   !}
    graduality-type-assign ctxwf precc (PIFailedCast prec x x₁) (TAFailedCast wt x₂ x₃ x₄) = {!   !}
    graduality-type-assign ctxwf precc (PIRemoveCast prec x x₁ x₂) (TACast wt x₃ x₄) = {!   !}
    graduality-type-assign ctxwf precc (PIAddCast prec wt1 prec1 prec2) wt2 with graduality-type-assign ctxwf precc prec wt2 
    ... | τ , wt3 , prec3 = _ , {!   !} , {!   !}
    graduality-type-assign ctxwf precc (PIBlame wt1 prect) (TAFailedCast wt2 gnd1 gnd2 neq) = _ , wt1 , prect