open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core
open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet
-- open import debruijn.debruijn-lemmas-wf
-- open import debruijn.debruijn-typed-elaboration

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
    ... | τ'' , match' , prec' = _ , STAp (⊑t-wf wf prect) syn' match' refl , {!   !} -- ⊑t-TTsub prect prec'

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

  ⊑t-ana : ∀{Θ Γ e τ d τ'} → Θ , Γ ⊢ e ⇐ τ ~> d :: τ' → τ' ⊑t τ
  ⊑t-ana (EALam MAHole ana) = PTHole
  ⊑t-ana {Θ = Θ} {Γ = Γ} (EALam MAArr ana) = PTArr (⊑t-ana {Θ = Θ} {Γ = Γ} EAEHole) (⊑t-ana ana)
  ⊑t-ana (EATLam neq1 neq2 MFHole ana) = PTHole
  ⊑t-ana (EATLam neq1 neq2 MFForall ana) = PTForall (⊑t-ana ana)
  ⊑t-ana (EASubsume neq1 neq2 syn meet) = π1 (⊓-lb meet)
  ⊑t-ana EAEHole = ⊑t-refl _
  ⊑t-ana (EANEHole _) = ⊑t-refl _

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

  mutual 
      
    graduality-elab-ana : 
      ∀{e e' τ1 τ2 τ1' Γ Γ' Θ d} →     
      (Γ ⊑c Γ') →
      (τ1 ⊑t τ1') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
      Σ[ d' ∈ ihexp ] Σ[ τ2' ∈ htyp ] ((Θ , Γ' ⊢ e' ⇐ τ1' ~> d' :: τ2') × (Θ , Γ , Γ' ⊢ d ⊑i d') × (τ2 ⊑t τ2'))
    graduality-elab-ana {e' = e'} precc prect prec (EASubsume neq1 neq2 syn meet) with hole-or-not e' 
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 syn meet) | Inl refl = _ , _ , EAEHole , PIEHole , ⊑t-trans (π1 (⊓-lb meet)) prect
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 syn meet) | Inr (Inl (e' , refl)) with graduality-elab-syn precc prec syn | ⊓-lb meet 
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 (ESNEHole syn) meet) | Inr (Inl (e' , refl)) | τ' , d' , syn' , prec1 , prec2 | prect' , _
      = abort (neq2 _ refl)
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 syn meet) | Inr (Inr (neq3 , neq4)) with graduality-elab-syn precc prec syn | ⊓-lb meet
    graduality-elab-ana precc prect prec (EASubsume neq1 neq2 syn meet) | Inr (Inr (neq3 , neq4)) | τ2' , d' , syn' , prect1 , prec' | prect2 , prect3 with ⊑t-⊓ prect prect1 meet
    ... | τ3' , meet' , prect4  = _ , _ , EASubsume neq3 neq4 syn' meet' , PICast prec' prect1 prect4 , prect4
    graduality-elab-ana precc prect PEHole ana = _ , _ , EAEHole , PIEHole , ⊑t-trans (⊑t-ana ana) prect
    graduality-elab-ana precc prect (PLam1 prec) (EALam match ana) with ⊑t-▸arr match prect 
    ... | τ1' , τ2' , match' , prect1 , prect2 with graduality-elab-ana (PCExtend prect1 precc) prect2 prec ana 
    ... | d' , τ' , ana' , prec' , prect' = _ , _ , EALam match' ana' , PILam prec' prect1 , PTArr prect1 prect'

    graduality-elab-ana precc prect (PTLam prec) (EATLam neq1 neq2 match ana) with ⊑t-▸forall match prect
    graduality-elab-ana precc prect (PTLam prec) (EATLam neq1 neq2 match ana) | τ' , match' , prect1 with graduality-elab-ana precc prect1 prec ana
    graduality-elab-ana {e' = ·Λ e'} precc prect (PTLam prec) (EATLam neq1 neq2 match ana) | τ' , match' , prect1 | thing , thing2 , ana' , prec' , prect2 with hole-or-not e'
    graduality-elab-ana precc prect (PTLam prec) (EATLam neq1 neq2 match ana) | .⦇-⦈ , MFHole , prect1 | thing , thing2 , ana' , prec' , prect2 | Inl refl =  _ , _ , EASubsume (λ ()) (λ e' ()) (ESTLam ESEHole) MeetHoleL , PIAddCast (PITLam PIEHole) (TATLam {!   !}) {!   !} {!   !} , PTForall PTHole 
    graduality-elab-ana precc prect (PTLam prec) (EATLam neq1 neq2 match ana) | τ' , MFForall , prect1 | thing , thing2 , ana' , prec' , prect2 | Inl refl = {!   !} --_ , _ , EASubsume (λ ()) (λ e' ()) (ESTLam ESEHole) {!   !} , {!   !} , {!   !}
    ... | Inr (Inl (e' , refl)) = {!   !}
    ... | Inr (Inr (neq3 , neq4)) = _ , _ , EATLam neq3 neq4 match' ana' , PITLam prec' , PTForall prect2
    
    graduality-elab-ana precc prect (PNEHole prec) (EANEHole syn) with graduality-elab-syn precc prec syn 
    ... | τ' , d' , syn' , prect' , prec' = _ , _ , EANEHole syn' , PINEHole prec' prect , prect

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
    graduality-elab-syn precc (PLam2 prec x) (ESLam wf elab) with graduality-elab-syn (PCExtend x precc) prec elab 
    ... | τ' , d' , elab' , prect , prec' = _ , _ , ESLam (⊑t-wf wf x) elab' , PTArr x prect , PILam prec' x
    graduality-elab-syn precc (PTLam prec) (ESTLam elab) with graduality-elab-syn precc prec elab 
    ... | τ' , d' , elab' , prect , prec' = _ , _ , ESTLam elab' , PTForall prect , PITLam prec'
    graduality-elab-syn precc (PNEHole prec) (ESNEHole elab) with graduality-elab-syn precc prec elab 
    ... | τ' , d' , elab' , prect , prec' = _ , _ , ESNEHole elab' , PTHole , PINEHole prec' PTHole
    graduality-elab-syn precc (PAp prec1 prec2) (ESAp syn match ana1 ana2) with graduality-syn precc prec1 syn 
    ... | τ1' , syn' , prec1' with ⊑t-▸arr match prec1' 
    ... | τ2' , τ' , match' , prec3 , prec4 with graduality-elab-ana precc (PTArr prec3 prec4) prec1 ana1 
    ... | d1' , τ1''' , ana1' , prec5 , prec6 with graduality-elab-ana precc prec3 prec2 ana2 
    ... | d2' , τ2''' , ana2' , prec7 , prec8 = _ , _ , (ESAp syn' match' ana1' ana2') , prec4 , PIAp (PICast prec5 prec6 (PTArr prec3 prec4)) (PICast prec7 prec8 prec3)
    graduality-elab-syn precc (PTAp prec prect) (ESTAp wf syn match ana sub) with graduality-syn precc prec syn 
    ... | τ4' , syn' , prec1 with ⊑t-▸forall match prec1 
    ... | τ4'' , match' , prec2 with graduality-elab-ana precc (PTForall prec2) prec ana 
    ... | d' , τ2'' , ana' , prec3 , prec4 rewrite (sym sub) = _ , _ , ESTAp (⊑t-wf wf prect) syn' match' ana' refl , {!   !} , PITAp (PICast prec3 prec4 (PTForall prec2)) prect
   