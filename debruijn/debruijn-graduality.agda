open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet

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
    graduality-ana precc prect (PLam1 prec) (ALam match ana) with ⊑t-▸arr match prect 
    ... | τ1 , τ2 , match' , prec1 , prec2 = ALam match' (graduality-ana (PCExtend prec1 precc) prec2 prec ana)
    graduality-ana precc prect (PTLam prec) (ATLam match ana) with ⊑t-▸forall match prect
    ... | τ' , match' , prec' = ATLam match' (graduality-ana precc prec' prec ana)
    
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
      = τ' , SAsc (⊑t-wf wf prect) (graduality-ana precc prect prec ana) , prect
    graduality-syn precc (PLam2 prec prect) (SLam wf syn) with graduality-syn (PCExtend prect precc) prec syn 
    ... | τ' , syn' , prect' = _ , SLam (⊑t-wf wf prect) syn' , PTArr prect prect'
    graduality-syn precc (PTLam prec) (STLam syn) with graduality-syn precc prec syn 
    ... | τ' , syn' , prect' = _ , STLam syn' , PTForall prect'
    graduality-syn precc (PNEHole prec) (SNEHole syn) with graduality-syn precc prec syn 
    ... | τ' , syn' , prect' = _ , SNEHole syn' , PTHole
    graduality-syn precc (PAp prec1 prec2) (SAp syn match ana) with graduality-syn precc prec1 syn
    ... | τ' , wt' , prect with ⊑t-▸arr match prect
    ... | τ1' , τ2' , match' , prec1' , prec2' = τ2' , SAp wt' match' (graduality-ana precc prec1' prec2 ana) , prec2'
    graduality-syn precc (PTAp {τ2 = τ2} prec prect) (STAp wf syn match subst) rewrite (sym subst) with graduality-syn precc prec syn 
    ... | τ' , syn' , prect' with ⊑t-▸forall match prect'
    ... | τ'' , match' , prec' = _ , STAp (⊑t-wf wf prect) syn' match' refl , ⊑t-TTsub prect prec'

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

  mutual 
      
    graduality-elab-ana : 
      ∀{e e' τ1 τ2 τ1' Γ Γ' Θ d} →     
      (Γ ⊑c Γ') →
      (τ1 ⊑t τ1') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
      Σ[ d' ∈ ihexp ] Σ[ τ2' ∈ htyp ] ((Θ , Γ' ⊢ e' ⇐ τ1' ~> d' :: τ2') × (Θ , Γ , Γ' ⊢ d ⊑i d') × (τ2 ⊑t τ2'))
    graduality-elab-ana {e' = ⦇-⦈} precc prect prec (EASubsume neq1 neq2 syn consist) with graduality-elab-syn precc prec syn | ⊓-lb consist
    graduality-elab-ana {e' = ⦇-⦈} precc prect prec (EASubsume neq1 neq2 syn consist) | τ' , d' , syn' , prec1 , prec2 | prect' , _
      = _ , _ , EAEHole , PIEHole , ⊑t-trans prect' prect
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 syn consist) with graduality-elab-syn precc prec syn | ⊓-lb consist
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 syn consist) | τ2' , d' , syn' , prect1 , prec' | prect2 , prect3
      = _ , _ , EASubsume {!   !} {!   !} syn' {!   !} , {!   !} , {!   !} -- PIRemoveCast prec' {!   !} prect1 (⊑t-trans prect3 prect1) , ⊑t-trans prect2 prect
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 syn consist) = {!   !}
    graduality-elab-ana precc prect prec (EALam x syn) = {!   !}
    graduality-elab-ana precc prect prec (EATLam x x₁ x₂ syn) = {!   !}
    graduality-elab-ana precc prect prec EAEHole = {!   !}
    graduality-elab-ana precc prect prec (EANEHole x) = {!   !}

    graduality-elab-syn : 
      ∀{e e' Γ Γ' Θ τ d} →     
      (Γ ⊑c Γ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e ⇒ τ ~> d) →
      Σ[ τ' ∈ htyp ] Σ[ d' ∈ ihexp ] ((Θ , Γ' ⊢ e' ⇒ τ' ~> d') × (τ ⊑t τ') × (Θ , Γ , Γ' ⊢ d ⊑i d'))
    graduality-elab-syn precc PEHole elab = ⦇-⦈ , ⦇-⦈⟨ ⦇-⦈ ⟩ , ESEHole , PTHole , PIEHole
    graduality-elab-syn precc PConst ESConst = b , c , ESConst , PTBase , PIConst
    graduality-elab-syn precc PVar (ESVar inctx) with ⊑c-var inctx precc
    ... | τ' , inctx' , prect = _ , _ , ESVar inctx' , prect , PIVar
    graduality-elab-syn precc (PAsc prec x) (ESAsc wf ana) with graduality-elab-ana precc x prec ana 
    ... | d' , τ2' , ana' , prec' , prect = _ , _ , ESAsc (⊑t-wf wf x) ana' , x , PICast prec' prect x
    graduality-elab-syn precc (PLam2 prec x) (ESLam wf elab) with graduality-elab-syn {!   !} prec elab 
    ... | τ' , d' , elab' , prect , prec' = _ , _ , ESLam (⊑t-wf wf x) elab' , PTArr x prect , PILam {!   !} x
    graduality-elab-syn precc (PTLam prec) (ESTLam elab) with graduality-elab-syn precc prec elab 
    ... | τ' , d' , elab' , prect , prec' = _ , _ , ESTLam elab' , PTForall prect , PITLam {!   !}
    graduality-elab-syn precc (PNEHole prec) (ESNEHole elab) with graduality-elab-syn precc prec elab 
    ... | τ' , d' , elab' , prect , prec' = _ , _ , ESNEHole elab' , PTHole , PINEHole prec'
    graduality-elab-syn precc (PAp prec1 prec2) (ESAp syn match ana1 ana2) with graduality-syn precc prec1 syn 
    ... | τ1' , syn' , prec1' with ⊑t-▸arr match prec1' 
    ... | τ2' , τ' , match' , prec3 , prec4 with graduality-elab-ana precc (PTArr prec3 prec4) prec1 ana1 
    ... | d1' , τ1''' , ana1' , prec5 , prec6 with graduality-elab-ana precc prec3 prec2 ana2 
    ... | d2' , τ2''' , ana2' , prec7 , prec8 = _ , _ , (ESAp syn' match' ana1' ana2') , prec4 , PIAp (PICast prec5 prec6 (PTArr prec3 prec4)) (PICast prec7 prec8 prec3)
    graduality-elab-syn precc (PTAp prec prect) (ESTAp wf syn match ana sub) with graduality-syn precc prec syn 
    ... | τ4' , syn' , prec1 with ⊑t-▸forall match prec1 
    ... | τ4'' , match' , prec2 with graduality-elab-ana precc (PTForall prec2) prec ana 
    ... | d' , τ2'' , ana' , prec3 , prec4 rewrite (sym sub) = _ , _ , ESTAp (⊑t-wf wf prect) syn' match' ana' refl , ⊑t-TTsub prect prec2 , PITAp (PICast prec3 prec4 (PTForall prec2)) prect
   