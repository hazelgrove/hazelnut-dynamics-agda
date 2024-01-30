open import Nat
open import Prelude
open import simple-core
open alpha
open import simple-lemmas-alpha
open import simple-lemmas-consistency

open import contexts

-- Note from Thomas: the draft paper is missing a definition of ⊑ for terms

module simple-graduality where

  data _⇓_ : (e : hexp) (v : ihexp) → Set where
    Converge : 
      ∀{e τ d v} → 
      ∅ , ∅ ⊢ e ⇒ τ ~> d → 
      d ↦* v → 
      v boxedval →
      e ⇓ v
  
  data _⇑ : (e : hexp) → Set where
    Diverge : 
      ∀{e τ d} → 
      ∅ , ∅ ⊢ e ⇒ τ ~> d → 
      (∀{v} → d ↦* v → v boxedval → ⊥) → 
      e ⇑

  data _⊑typ_ : (τ1 τ2 : htyp) → Set where 
    PTBase : b ⊑typ b 
    PTHole : ∀{τ} → τ ⊑typ ⦇-⦈     
    PTTVar : ∀{x} → (T x) ⊑typ (T x) 
    PTArr : ∀{τ1 τ2 τ3 τ4} → τ1 ⊑typ τ3 → τ2 ⊑typ τ4 → (τ1 ==> τ2) ⊑typ (τ3 ==> τ4) 
    PTForall : ∀{x τ1 τ2} → τ1 ⊑typ τ2 → (·∀ x τ1) ⊑typ (·∀ x τ2) 

  data _⊑_ : (e1 e2 : hexp) → Set where
    PConst : c ⊑ c
    PVar : ∀{x} → (X x) ⊑ (X x) 
    PAsc : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑typ τ2 → (e1 ·: τ1) ⊑ (e2 ·: τ2)
    PEHole : ∀{u e} → e ⊑ ⦇-⦈
    PLam1 : ∀{x e1 e2} → e1 ⊑ e2 → (·λ x e1) ⊑ (·λ x e2)
    PLam2 : ∀{x e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑typ τ2 → (·λ x [ τ1 ] e1) ⊑ (·λ x [ τ2 ] e2)
    PTLam : ∀{t e1 e2} → e1 ⊑ e2 → (·Λ t e1) ⊑ (·Λ t e2)
    PNEHole : ∀{u e1 e2} → e1 ⊑ e2 → (⦇⌜ e1 ⌟⦈) ⊑ (⦇⌜ e2 ⌟⦈)
    PAp :  ∀{e1 e2 e3 e4} → e1 ⊑ e3 → e2 ⊑ e4 → (e1 ∘ e2) ⊑ (e3 ∘ e4)
    PTAp : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑typ τ2 → (e1 < τ1 >) ⊑ (e2 < τ2 >)

  data _⊑i_ : (d1 d2 : ihexp) → Set where
    PIConst : c ⊑i c
    PIVar : ∀{x} → (X x) ⊑i (X x) 
    PIEHole : ∀{τ e} → e ⊑i ⦇-⦈⟨ τ ⟩
    PILam : ∀{x d1 d2 τ1 τ2} → d1 ⊑i d2 → τ1 ⊑typ τ2 → (·λ x [ τ1 ] d1) ⊑i (·λ x [ τ2 ] d2)
    PITLam : ∀{t d1 d2} → d1 ⊑i d2 → (·Λ t d1) ⊑i (·Λ t d2)
    PINEHole : ∀{τ d1 d2} → d1 ⊑i d2 →(⦇⌜ d1 ⌟⦈⟨ τ ⟩) ⊑i (⦇⌜ d2 ⌟⦈⟨ τ ⟩)
    PIAp :  ∀{d1 d2 d3 d4} → d1 ⊑i d3 → d2 ⊑i d4 → (d1 ∘ d2) ⊑i (d3 ∘ d4)
    PITAp : ∀{d1 d2 τ1 τ2} → d1 ⊑i d2 → τ1 ⊑typ τ2 → (d1 < τ1 >) ⊑i (d2 < τ2 >)
    PICast : ∀{d1 d2 τ1 τ2 τ3 τ4} → d1 ⊑i d2 → τ1 ⊑typ τ3 → τ2 ⊑typ τ4 → (d1 ⟨ τ1 ⇒ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒ τ4 ⟩)
    PIFailedCast : ∀{d1 d2 τ1 τ2 τ3 τ4} → d1 ⊑i d2 → τ1 ⊑typ τ3 → τ2 ⊑typ τ4 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒⦇-⦈⇏ τ4 ⟩)

  _⊑ctx_ : (Γ1 Γ2 : tctx) → Set 
  Γ1 ⊑ctx Γ2 = (∀{x τ1 τ2} → (x , τ1) ∈ Γ1 → (x , τ2) ∈ Γ2 → (τ1 ⊑typ τ2)) × (∀{x} → x # Γ1 → x # Γ2) × (∀{x} → x # Γ2 → x # Γ1)

  ⊑typ-refl : ∀{τ} → τ ⊑typ τ
  ⊑typ-refl {τ = b} = PTBase
  ⊑typ-refl {τ = T x} = PTTVar
  ⊑typ-refl {τ = ⦇-⦈} = PTHole
  ⊑typ-refl {τ = τ ==> τ₁} = PTArr ⊑typ-refl ⊑typ-refl
  ⊑typ-refl {τ = ·∀ x τ} = PTForall ⊑typ-refl

  ⊑typ-wf : ∀{Θ τ1 τ2} → Θ ⊢ τ1 wf → τ1 ⊑typ τ2 → Θ ⊢ τ2 wf
  ⊑typ-wf wf PTBase = wf
  ⊑typ-wf wf PTHole = WFHole
  ⊑typ-wf wf PTTVar = wf
  ⊑typ-wf (WFArr wf wf₁) (PTArr prec prec₁) = WFArr (⊑typ-wf wf prec) (⊑typ-wf wf₁ prec₁)
  ⊑typ-wf (WFForall apt wf) (PTForall prec) = WFForall apt (⊑typ-wf wf prec)

  ⊑typ-consist-helper : ∀{τ τ' τ'' ΓL ΓR} → ΓL , ΓR ⊢ τ ~ τ' → τ ⊑typ τ'' → ΓL , ΓR ⊢ τ'' ~ τ'
  ⊑typ-consist-helper ConsistHole1 prec = ConsistHole1
  ⊑typ-consist-helper consist PTBase = consist
  ⊑typ-consist-helper consist PTHole = ConsistHole2
  ⊑typ-consist-helper consist PTTVar = consist
  ⊑typ-consist-helper (ConsistArr consist consist₁) (PTArr prec prec₁) = ConsistArr (⊑typ-consist-helper consist prec) (⊑typ-consist-helper consist₁ prec₁)
  ⊑typ-consist-helper (ConsistForall consist) (PTForall prec) = ConsistForall (⊑typ-consist-helper consist prec)

  ⊑typ-consist : ∀{τ τ' τ''} → τ ~ τ' → τ ⊑typ τ'' → τ'' ~ τ'
  ⊑typ-consist consist prec = ⊑typ-consist-helper consist prec

  ⊑typ-consist-right : ∀{τ τ' τ''} → τ ~ τ' → τ' ⊑typ τ'' → τ ~ τ''
  ⊑typ-consist-right consist prec = ~sym (⊑typ-consist (~sym consist) prec)

  ⊑typ-▸arr : ∀{τ τ' τ1 τ2} → τ ▸arr (τ1 ==> τ2) → τ ⊑typ τ' → Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ] ((τ' ▸arr (τ1' ==> τ2')) × (τ1 ⊑typ τ1') × (τ2 ⊑typ τ2'))
  ⊑typ-▸arr match PTHole = ⦇-⦈ , ⦇-⦈ , MAHole , PTHole , PTHole
  ⊑typ-▸arr MAArr (PTArr prec prec₁) = _ , _ , MAArr , prec , prec₁

  ⊑typ-▸forall : ∀{t τ1 τ1' τ2} → τ1 ▸forall (·∀ t τ2) → τ1 ⊑typ τ1' → Σ[ τ2' ∈ htyp ] ((τ1' ▸forall (·∀ t τ2')) × (τ2 ⊑typ τ2'))
  ⊑typ-▸forall match PTHole = ⦇-⦈ , MFHole , PTHole
  ⊑typ-▸forall MFForall (PTForall prec) = _ , MFForall , prec

  ⊑typ-Typsubst : ∀{t τ1 τ2 τ3 τ4} → (τ1 ⊑typ τ3) → (τ2 ⊑typ τ4) → (Typ[ τ1 / t ] τ2) ⊑typ (Typ[ τ3 / t ] τ4)
  ⊑typ-Typsubst prec1 PTBase = PTBase
  ⊑typ-Typsubst prec1 PTHole = PTHole
  ⊑typ-Typsubst {t = t} prec1 (PTTVar {x = x}) with natEQ t x 
  ... | Inl refl = prec1 
  ... | Inr x = PTTVar
  ⊑typ-Typsubst prec1 (PTArr prec2 prec3) = PTArr (⊑typ-Typsubst prec1 prec2) (⊑typ-Typsubst prec1 prec3)
  ⊑typ-Typsubst {t = t} prec1 (PTForall {x = x} prec2) with natEQ t x 
  ... | Inl refl = PTForall prec2 
  ... | Inr x = PTForall (⊑typ-Typsubst prec1 prec2)

  ⊑ctx-var : ∀{x τ Γ Γ'} → (x , τ) ∈ Γ → Γ ⊑ctx Γ' → Σ[ τ' ∈ htyp ] (((x , τ') ∈ Γ') × (τ ⊑typ τ'))
  ⊑ctx-var {x = x} {Γ = Γ} {Γ' = Γ'} inctx ( precctx , apt1 , apt2 ) with Γ' x in eq'
  ... | Some τ' = τ' ,  refl , precctx inctx eq' 
  ... | None rewrite (apt2 eq') with inctx 
  ... | () 

  apt-lem : ∀{y x τ τ'} → (Γa Γb : tctx) → ((z : Nat) → z # Γa → z # Γb) → y # (Γa ,, (x , τ)) → y # (Γb ,, (x , τ'))
  apt-lem {y = y} Γa Γb apts aptarg with Γa y in eq | Γb y in eq'
  apt-lem {y = y} Γa Γb apts aptarg | None | Some x rewrite (apts y eq) = sym eq'
  apt-lem {y = y} {x = x} Γa Γb apts aptarg | None | None with natEQ x y 
  apt-lem {y = y} Γa Γb apts () | None | None | Inl refl
  ... | Inr x = refl

  other-lem : ∀{x z τ τ' τ1 τ2} → (Γ Γ' : tctx) → ((w : Nat) → w # Γ → w # Γ') → ((w : Nat) → w # Γ' → w # Γ) → ({y : Nat} {τy τy' : htyp} → (y , τy) ∈ Γ → (y , τy') ∈ Γ' → τy ⊑typ τy') → (x , τ1) ∈ (Γ ,, (z , τ)) → (x , τ2) ∈ (Γ' ,, (z , τ')) → (τ ⊑typ τ') → τ1 ⊑typ τ2
  other-lem {x = x} Γ Γ' apt1 apt2 ind in1 in2 prectyp with Γ x in eq | Γ' x in eq' 
  other-lem {_} Γ Γ' apt1 apt2 ind in1 in2 prectyp | Some thing | Some thing' rewrite in1 rewrite in2 = ind eq eq'
  other-lem {_} Γ Γ' apt1 apt2 ind in1 in2 prectyp | Some thing | None rewrite (apt2 _ eq') with eq 
  ... | () 
  other-lem {_} Γ Γ' apt1 apt2 ind in1 in2 prectyp | None | Some thing rewrite (apt1 _ eq) with eq' 
  ... | () 
  other-lem {x = x} {z = z} Γ Γ' apt1 apt2 ind in1 in2 prectyp | None | None with natEQ z x | in1 | in2
  ... | Inl refl | refl | refl = prectyp
  ... | Inr x | () | () 

  ⊑ctx-entend : ∀{Γ x τ Γ' τ'} → (Γ ⊑ctx Γ') → (τ ⊑typ τ') → (Γ ,, (x , τ)) ⊑ctx (Γ' ,, (x , τ'))
  ⊑ctx-entend {Γ = Γ} {x = x} {τ = τ} {Γ' = Γ'} {τ' = τ'} ( precctx , apt1 , apt2 ) prectyp = ( ((λ x₁ x₂ → other-lem Γ Γ' (λ w → apt1) (λ w → apt2) precctx x₁ x₂ prectyp)) , (λ {y : Nat} → λ apt → apt-lem Γ Γ' (λ z → apt1) apt) , (λ {y : Nat} → λ apt → apt-lem Γ' Γ (λ z → apt2) apt) ) 
  ∅⊑ctx∅ : ∅ ⊑ctx ∅
  ∅⊑ctx∅ = ((λ x ()) , (λ x → refl) , (λ x → refl))

  mutual

    graduality-ana : 
      ∀{τ τ' e e' Θ Γ Γ'} →
      (Γ ⊑ctx Γ') →
      (τ ⊑typ τ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e <= τ) →
      (Θ , Γ' ⊢ e' <= τ')
      
    graduality-ana precctx prectyp prec (ASubsume syn consist) 
      with graduality-syn precctx prec syn 
    ... | τ' , syn' , prectyp' = ASubsume syn' (⊑typ-consist (⊑typ-consist-right consist prectyp') prectyp)
    graduality-ana precctx prectyp PEHole ana = ASubsume SEHole ConsistHole1
    graduality-ana precctx prectyp (PLam1 prec) (ALam x x₁ ana) 
      with ⊑typ-▸arr x₁ prectyp | precctx
    ... | τ1 , τ2 , match , prec1 , prec2 | precctxpt , apt1 , apt2 
      = ALam (apt1 x) match (graduality-ana (⊑ctx-entend precctx prec1) prec2 prec ana)
    graduality-ana precctx prectyp (PTLam prec) (ATLam x ana) 
      with ⊑typ-▸forall x prectyp
    ... | τ' , match , prec' = ATLam match (graduality-ana precctx prec' prec ana)
    
    graduality-syn : 
      ∀{e e' Θ Γ Γ' τ} →
      (Γ ⊑ctx Γ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e => τ) →
      Σ[ τ' ∈ htyp ] ((Θ , Γ' ⊢ e' => τ') × (τ ⊑typ τ'))
    graduality-syn precctx PConst SConst = b , SConst , PTBase
    graduality-syn precctx PVar (SVar inctx) with ⊑ctx-var inctx precctx
    ... | τ' , inctx' , prectyp = τ' , SVar inctx' , prectyp
    graduality-syn {e' = e' ·: τ'} precctx (PAsc prec x) (SAsc x₁ x₂) = τ' , SAsc (⊑typ-wf x₁ x) (graduality-ana precctx x prec x₂) , x
    graduality-syn precctx PEHole wt = ⦇-⦈ , SEHole , PTHole
    graduality-syn ( precctx , apt1 , apt2 ) (PLam2 {τ2 = τ2} prec x) (SLam x₁ x₂ wt) 
      with graduality-syn (⊑ctx-entend ( precctx , apt1 , apt2 ) x) prec wt 
    ... | τ' , wt' , prectyp = τ2 ==> τ' , (SLam (apt1 x₁) (⊑typ-wf x₂ x) wt') , PTArr x prectyp
    graduality-syn precctx (PTLam {t = t} prec) (STLam wt)
      with graduality-syn precctx prec wt 
    ... | τ' , wt' , prectyp = ·∀ t τ' , STLam wt' , PTForall prectyp
    graduality-syn precctx (PNEHole prec) (SNEHole wt) 
      with graduality-syn precctx prec wt 
    ... | τ' , wt' , prectyp = ⦇-⦈ , SNEHole wt' , PTHole
    graduality-syn precctx (PAp prec prec₁) (SAp syn match ana) 
      with graduality-syn precctx prec syn
    ... | τ' , wt' , prectyp 
      with ⊑typ-▸arr match prectyp 
    ... | τ1' , τ2' , match' , prec1' , prec2' = τ2' , SAp wt' match' (graduality-ana precctx prec1' prec₁ ana) , prec2'
    graduality-syn precctx (PTAp {τ2 = τ2} prec x) (STAp {t = t} x₁ wt x₂ x₃) rewrite (sym x₃) 
      with graduality-syn precctx prec wt 
    ... | τ' , wt' , prectyp 
      with ⊑typ-▸forall x₂ prectyp 
    ... | τ'' , match , prec' = Typ[ τ2 / t ] τ'' , STAp (⊑typ-wf x₁ x) wt' match refl , ⊑typ-Typsubst x prec'
 
  graduality1 : 
    ∀{e e' τ} →     
    (e ⊑ e') →
    (∅ , ∅ ⊢ e => τ) →
    Σ[ τ' ∈ htyp ] ((∅ , ∅ ⊢ e' => τ') × (τ ⊑typ τ'))
  graduality1 prec wt = graduality-syn ∅⊑ctx∅ prec wt  

  -- not true
  -- elaboration-specifies : 
  --   ∀{e τ1 τ2 Γ Θ d} →
  --   (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
  --   (τ2 ⊑typ τ1)
  -- elaboration-specifies (EALam x x₁ ana) = {!   !}
  -- elaboration-specifies (EATLam x x₁ x₂ ana) = {!   !}
  -- elaboration-specifies (EASubsume x x₁ syn consist) = {!   !}
  -- elaboration-specifies EAEHole = ⊑typ-refl
  -- elaboration-specifies (EANEHole x) = ⊑typ-refl

  mutual 
      
    graduality-elab-ana : 
      ∀{e e' τ1 τ2 τ1' Γ Γ' Θ d} →     
      (Γ ⊑ctx Γ') →
      (τ1 ⊑typ τ1') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
      Σ[ d' ∈ ihexp ] Σ[ τ2' ∈ htyp ] ((Θ , Γ' ⊢ e' ⇐ τ1' ~> d' :: τ2') × (d ⊑i d') × (τ2 ⊑typ τ2'))
    graduality-elab-ana {e' = ⦇-⦈} precctx prectyp prec (EASubsume neq1 neq2 syn consist) with graduality-elab-syn precctx prec syn 
    graduality-elab-ana {e' = ⦇-⦈} precctx prectyp prec (EASubsume neq1 neq2 syn consist) | τ' , d' , syn' , prec1 , prec2 = _ , _ , EAEHole , PIEHole , {!   !}
    graduality-elab-ana precctx prectyp prec syn = {!   !}

    graduality-elab-syn : 
      ∀{e e' Γ Γ' Θ τ d} →     
      (Γ ⊑ctx Γ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e ⇒ τ ~> d) →
      Σ[ τ' ∈ htyp ] Σ[ d' ∈ ihexp ] ((Θ , Γ' ⊢ e' ⇒ τ' ~> d') × (τ ⊑typ τ') × (d ⊑i d'))
    graduality-elab-syn {Γ' = Γ'} {Θ = Θ} precctx (PEHole {u = u}) elab = ⦇-⦈ , ⦇-⦈⟨ ⦇-⦈ ⟩ , ESEHole , PTHole , PIEHole
    graduality-elab-syn precctx PConst ESConst = b , c , ESConst , PTBase , PIConst
    graduality-elab-syn precctx PVar (ESVar inctx) with ⊑ctx-var inctx precctx
    ... | τ' , inctx' , prectyp = _ , _ , ESVar inctx' , prectyp , PIVar
    graduality-elab-syn precctx (PAsc prec x) (ESAsc wf ana) with graduality-elab-ana precctx x prec ana 
    ... | d' , τ2' , ana' , prec' , prectyp = _ , _ , ESAsc (⊑typ-wf wf x) ana' , x , PICast prec' prectyp x
    graduality-elab-syn ( precctx , apt1 , apt2 ) (PLam2 prec x) (ESLam apt wf elab) with graduality-elab-syn (⊑ctx-entend ( precctx , apt1 , apt2 ) x) prec elab 
    ... | τ' , d' , elab' , prectyp , prec' = _ , _ , ESLam (apt1 apt) (⊑typ-wf wf x) elab' , PTArr x prectyp , PILam prec' x
    graduality-elab-syn precctx (PTLam prec) (ESTLam elab) with graduality-elab-syn precctx prec elab 
    ... | τ' , d' , elab' , prectyp , prec' = _ , _ , ESTLam elab' , PTForall prectyp , PITLam prec'
    graduality-elab-syn precctx (PNEHole prec) (ESNEHole elab) with graduality-elab-syn precctx prec elab 
    ... | τ' , d' , elab' , prectyp , prec' = _ , _ , ESNEHole elab' , PTHole , PINEHole prec'
    graduality-elab-syn precctx (PAp prec1 prec2) (ESAp syn match ana1 ana2) with graduality-syn precctx prec1 syn 
    ... | τ1' , syn' , prec1' with ⊑typ-▸arr match prec1' 
    ... | τ2' , τ' , match' , prec3 , prec4 with graduality-elab-ana precctx (PTArr prec3 prec4) prec1 ana1 
    ... | d1' , τ1''' , ana1' , prec5 , prec6 with graduality-elab-ana precctx prec3 prec2 ana2 
    ... | d2' , τ2''' , ana2' , prec7 , prec8 = _ , _ , (ESAp syn' match' ana1' ana2') , prec4 , PIAp (PICast prec5 prec6 (PTArr prec3 prec4)) (PICast prec7 prec8 prec3)
    graduality-elab-syn precctx (PTAp prec prectyp) (ESTAp wf syn match ana sub) with graduality-syn precctx prec syn 
    ... | τ4' , syn' , prec1 with ⊑typ-▸forall match prec1 
    ... | τ4'' , match' , prec2 with graduality-elab-ana precctx (PTForall prec2) prec ana 
    ... | d' , τ2'' , ana' , prec3 , prec4 rewrite (sym sub) = _ , _ , ESTAp (⊑typ-wf wf prectyp) syn' match' ana' refl , ⊑typ-Typsubst prectyp prec2 , PITAp (PICast prec3 prec4 (PTForall prec2)) prectyp
   
  graduality2 : 
    ∀{e e' v} →     
    (e ⊑ e') →
    (e ⇓ v) → 
    Σ[ v' ∈ ihexp ] ((e' ⇓ v') × (v ⊑i v'))
  graduality2 prec (Converge elab steps bv) with graduality-elab-syn ∅⊑ctx∅ prec elab 
  ... | τ' , d' , elab' , prectyp  , precd with steps 
  ... | MSRefl = d' , Converge elab' MSRefl {!   !} , precd 
  ... | MSStep x stepsss = {!   !}