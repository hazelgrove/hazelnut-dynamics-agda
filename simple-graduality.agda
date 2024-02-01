open import Nat
open import Prelude
open import contexts
open import simple-core
open import simple-lemmas-alpha
open import simple-lemmas-consistency


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

  data _⊑_ : (e1 e2 : hexp) → Set where
    PConst : c ⊑ c
    PVar : ∀{x} → (X x) ⊑ (X x) 
    PAsc : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑t τ2 → (e1 ·: τ1) ⊑ (e2 ·: τ2)
    PEHole : ∀{e} → e ⊑ ⦇-⦈
    PLam1 : ∀{x e1 e2} → e1 ⊑ e2 → (·λ x e1) ⊑ (·λ x e2)
    PLam2 : ∀{x e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑t τ2 → (·λ x [ τ1 ] e1) ⊑ (·λ x [ τ2 ] e2)
    PTLam : ∀{t e1 e2} → e1 ⊑ e2 → (·Λ t e1) ⊑ (·Λ t e2)
    PNEHole : ∀{e1 e2} → e1 ⊑ e2 → (⦇⌜ e1 ⌟⦈) ⊑ (⦇⌜ e2 ⌟⦈)
    PAp :  ∀{e1 e2 e3 e4} → e1 ⊑ e3 → e2 ⊑ e4 → (e1 ∘ e2) ⊑ (e3 ∘ e4)
    PTAp : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑t τ2 → (e1 < τ1 >) ⊑ (e2 < τ2 >)

  -- see Refined Criteria for Gradual Typing, Figure 9
  data _,_,_⊢_⊑i_ : (Θ : typctx) → (Γ : tctx) → (Γ' : tctx) → (d1 d2 : ihexp) → Set where
    PIConst : ∀{Θ Γ Γ'} → Θ , Γ , Γ' ⊢ c ⊑i c
    PIVar : ∀{Θ Γ Γ' x} → Θ , Γ , Γ' ⊢ (X x) ⊑i (X x) 
    PIEHole : ∀{Θ Γ Γ' τ d} → Θ , Γ , Γ' ⊢ d ⊑i ⦇-⦈⟨ τ ⟩
    PILam : ∀{Θ Γ Γ' x d1 d2 τ1 τ2} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ2 → Θ , Γ , Γ' ⊢ (·λ x [ τ1 ] d1) ⊑i (·λ x [ τ2 ] d2)
    PITLam : ∀{Θ Γ Γ' t d1 d2} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → Θ , Γ , Γ' ⊢ (·Λ t d1) ⊑i (·Λ t d2)
    PINEHole : ∀{Θ Γ Γ' τ d1 d2} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → Θ , Γ , Γ' ⊢ (⦇⌜ d1 ⌟⦈⟨ τ ⟩) ⊑i (⦇⌜ d2 ⌟⦈⟨ τ ⟩)
    PIAp :  ∀{Θ Γ Γ' d1 d2 d3 d4} → Θ , Γ , Γ' ⊢ d1 ⊑i d3 → Θ , Γ , Γ' ⊢ d2 ⊑i d4 → Θ , Γ , Γ' ⊢ (d1 ∘ d2) ⊑i (d3 ∘ d4)
    PITAp : ∀{Θ Γ Γ' d1 d2 τ1 τ2} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ2 → Θ , Γ , Γ' ⊢ (d1 < τ1 >) ⊑i (d2 < τ2 >)
    PICast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ3 τ4} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ3 → τ2 ⊑t τ4 → Θ , Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒ τ4 ⟩)
    PIFailedCast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ3 τ4} → Θ , Γ , Γ' ⊢ d1 ⊑i d2 → τ1 ⊑t τ3 → τ2 ⊑t τ4 → Θ , Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⊑i (d2 ⟨ τ3 ⇒⦇-⦈⇏ τ4 ⟩)
    PIRemoveCast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ} → (Θ , Γ , Γ' ⊢ d1 ⊑i d2) → (Θ , Γ' ⊢ d2 :: τ) → (τ1 ⊑t τ) → (τ2 ⊑t τ) → Θ , Γ , Γ' ⊢ (d1 ⟨ τ1 ⇒ τ2 ⟩) ⊑i d2 
    PIAddCast : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ} → (Θ , Γ , Γ' ⊢ d1 ⊑i d2) → (Θ , Γ ⊢ d1 :: τ) → (τ ⊑t τ1) → (τ ⊑t τ2) → Θ , Γ , Γ' ⊢ d1 ⊑i (d2 ⟨ τ1 ⇒ τ2 ⟩) 
    PIBlame : ∀{Θ Γ Γ' d1 d2 τ1 τ2 τ} → (Θ , Γ' ⊢ d2 :: τ) → (τ2 ⊑t τ) → (Θ , Γ , Γ' ⊢ d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ⊑i d2)

  _⊑ctx_ : (Γ1 Γ2 : tctx) → Set 
  Γ1 ⊑ctx Γ2 = (∀{x τ1 τ2} → (x , τ1) ∈ Γ1 → (x , τ2) ∈ Γ2 → (τ1 ⊑t τ2)) × (∀{x} → x # Γ1 → x # Γ2) × (∀{x} → x # Γ2 → x # Γ1)

  ⊑t-refl : ∀{τ} → τ ⊑t τ
  ⊑t-refl {τ = b} = PTBase
  ⊑t-refl {τ = T x} = PTTVar
  ⊑t-refl {τ = ⦇-⦈} = PTHole
  ⊑t-refl {τ = τ ==> τ₁} = PTArr ⊑t-refl ⊑t-refl
  ⊑t-refl {τ = ·∀ x τ} = PTForall ⊑t-refl

  ⊑t-wf : ∀{Θ τ1 τ2} → Θ ⊢ τ1 wf → τ1 ⊑t τ2 → Θ ⊢ τ2 wf
  ⊑t-wf wf PTBase = wf
  ⊑t-wf wf PTHole = WFHole
  ⊑t-wf wf PTTVar = wf
  ⊑t-wf (WFArr wf wf₁) (PTArr prec prec₁) = WFArr (⊑t-wf wf prec) (⊑t-wf wf₁ prec₁)
  ⊑t-wf (WFForall apt wf) (PTForall prec) = WFForall apt (⊑t-wf wf prec)

  ⊑t-consist-helper : ∀{τ τ' τ'' ΓL ΓR} → ΓL , ΓR ⊢ τ ~ τ' → τ ⊑t τ'' → ΓL , ΓR ⊢ τ'' ~ τ'
  ⊑t-consist-helper ConsistHole1 prec = ConsistHole1
  ⊑t-consist-helper consist PTBase = consist
  ⊑t-consist-helper consist PTHole = ConsistHole2
  ⊑t-consist-helper consist PTTVar = consist
  ⊑t-consist-helper (ConsistArr consist consist₁) (PTArr prec prec₁) = ConsistArr (⊑t-consist-helper consist prec) (⊑t-consist-helper consist₁ prec₁)
  ⊑t-consist-helper (ConsistForall consist) (PTForall prec) = ConsistForall (⊑t-consist-helper consist prec)

  ⊑t-consist : ∀{τ τ' τ''} → τ ~ τ' → τ ⊑t τ'' → τ'' ~ τ'
  ⊑t-consist consist prec = ⊑t-consist-helper consist prec

  ⊑t-consist-right : ∀{τ τ' τ''} → τ ~ τ' → τ' ⊑t τ'' → τ ~ τ''
  ⊑t-consist-right consist prec = ~sym (⊑t-consist (~sym consist) prec)

  ⊑t-▸arr : ∀{τ τ' τ1 τ2} → τ ▸arr (τ1 ==> τ2) → τ ⊑t τ' → Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ] ((τ' ▸arr (τ1' ==> τ2')) × (τ1 ⊑t τ1') × (τ2 ⊑t τ2'))
  ⊑t-▸arr match PTHole = ⦇-⦈ , ⦇-⦈ , MAHole , PTHole , PTHole
  ⊑t-▸arr MAArr (PTArr prec prec₁) = _ , _ , MAArr , prec , prec₁

  ⊑t-▸forall : ∀{t τ1 τ1' τ2} → τ1 ▸forall (·∀ t τ2) → τ1 ⊑t τ1' → Σ[ τ2' ∈ htyp ] ((τ1' ▸forall (·∀ t τ2')) × (τ2 ⊑t τ2'))
  ⊑t-▸forall match PTHole = ⦇-⦈ , MFHole , PTHole
  ⊑t-▸forall MFForall (PTForall prec) = _ , MFForall , prec

  ⊑t-Typsubst : ∀{t τ1 τ2 τ3 τ4} → (τ1 ⊑t τ3) → (τ2 ⊑t τ4) → (Typ[ τ1 / t ] τ2) ⊑t (Typ[ τ3 / t ] τ4)
  ⊑t-Typsubst prec1 PTBase = PTBase
  ⊑t-Typsubst prec1 PTHole = PTHole
  ⊑t-Typsubst {t = t} prec1 (PTTVar {x = x}) with natEQ t x 
  ... | Inl refl = prec1 
  ... | Inr x = PTTVar
  ⊑t-Typsubst prec1 (PTArr prec2 prec3) = PTArr (⊑t-Typsubst prec1 prec2) (⊑t-Typsubst prec1 prec3)
  ⊑t-Typsubst {t = t} prec1 (PTForall {x = x} prec2) with natEQ t x 
  ... | Inl refl = PTForall prec2 
  ... | Inr x = PTForall (⊑t-Typsubst prec1 prec2)

  ⊑ctx-var : ∀{x τ Γ Γ'} → (x , τ) ∈ Γ → Γ ⊑ctx Γ' → Σ[ τ' ∈ htyp ] (((x , τ') ∈ Γ') × (τ ⊑t τ'))
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

  other-lem : ∀{x z τ τ' τ1 τ2} → (Γ Γ' : tctx) → ((w : Nat) → w # Γ → w # Γ') → ((w : Nat) → w # Γ' → w # Γ) → ({y : Nat} {τy τy' : htyp} → (y , τy) ∈ Γ → (y , τy') ∈ Γ' → τy ⊑t τy') → (x , τ1) ∈ (Γ ,, (z , τ)) → (x , τ2) ∈ (Γ' ,, (z , τ')) → (τ ⊑t τ') → τ1 ⊑t τ2
  other-lem {x = x} Γ Γ' apt1 apt2 ind in1 in2 prectyp with Γ x in eq | Γ' x in eq' 
  other-lem {_} Γ Γ' apt1 apt2 ind in1 in2 prectyp | Some thing | Some thing' rewrite in1 rewrite in2 = ind eq eq'
  other-lem {_} Γ Γ' apt1 apt2 ind in1 in2 prectyp | Some thing | None rewrite (apt2 _ eq') with eq 
  ... | () 
  other-lem {_} Γ Γ' apt1 apt2 ind in1 in2 prectyp | None | Some thing rewrite (apt1 _ eq) with eq' 
  ... | () 
  other-lem {x = x} {z = z} Γ Γ' apt1 apt2 ind in1 in2 prectyp | None | None with natEQ z x | in1 | in2
  ... | Inl refl | refl | refl = prectyp
  ... | Inr x | () | () 

  ⊑ctx-entend : ∀{Γ x τ Γ' τ'} → (Γ ⊑ctx Γ') → (τ ⊑t τ') → (Γ ,, (x , τ)) ⊑ctx (Γ' ,, (x , τ'))
  ⊑ctx-entend {Γ = Γ} {x = x} {τ = τ} {Γ' = Γ'} {τ' = τ'} ( precctx , apt1 , apt2 ) prectyp = ( ((λ x₁ x₂ → other-lem Γ Γ' (λ w → apt1) (λ w → apt2) precctx x₁ x₂ prectyp)) , (λ {y : Nat} → λ apt → apt-lem Γ Γ' (λ z → apt1) apt) , (λ {y : Nat} → λ apt → apt-lem Γ' Γ (λ z → apt2) apt) ) 
  ∅⊑ctx∅ : ∅ ⊑ctx ∅
  ∅⊑ctx∅ = ((λ x ()) , (λ x → refl) , (λ x → refl))

  mutual

    graduality-ana : 
      ∀{τ τ' e e' Θ Γ Γ'} →
      (Γ ⊑ctx Γ') →
      (τ ⊑t τ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e <= τ) →
      (Θ , Γ' ⊢ e' <= τ')
      
    graduality-ana precctx prectyp prec (ASubsume syn consist) 
      with graduality-syn precctx prec syn 
    ... | τ' , syn' , prectyp' = ASubsume syn' (⊑t-consist (⊑t-consist-right consist prectyp') prectyp)
    graduality-ana precctx prectyp PEHole ana = ASubsume SEHole ConsistHole1
    graduality-ana precctx prectyp (PLam1 prec) (ALam x x₁ ana) 
      with ⊑t-▸arr x₁ prectyp | precctx
    ... | τ1 , τ2 , match , prec1 , prec2 | precctxpt , apt1 , apt2 
      = ALam (apt1 x) match (graduality-ana (⊑ctx-entend precctx prec1) prec2 prec ana)
    graduality-ana precctx prectyp (PTLam prec) (ATLam x ana) 
      with ⊑t-▸forall x prectyp
    ... | τ' , match , prec' = ATLam match (graduality-ana precctx prec' prec ana)
    
    graduality-syn : 
      ∀{e e' Θ Γ Γ' τ} →
      (Γ ⊑ctx Γ') →
      (e ⊑ e') →
      (Θ , Γ ⊢ e => τ) →
      Σ[ τ' ∈ htyp ] ((Θ , Γ' ⊢ e' => τ') × (τ ⊑t τ'))
    graduality-syn precctx PConst SConst = b , SConst , PTBase
    graduality-syn precctx PVar (SVar inctx) with ⊑ctx-var inctx precctx
    ... | τ' , inctx' , prectyp = τ' , SVar inctx' , prectyp
    graduality-syn {e' = e' ·: τ'} precctx (PAsc prec x) (SAsc x₁ x₂) = τ' , SAsc (⊑t-wf x₁ x) (graduality-ana precctx x prec x₂) , x
    graduality-syn precctx PEHole wt = ⦇-⦈ , SEHole , PTHole
    graduality-syn ( precctx , apt1 , apt2 ) (PLam2 {τ2 = τ2} prec x) (SLam x₁ x₂ wt) 
      with graduality-syn (⊑ctx-entend ( precctx , apt1 , apt2 ) x) prec wt 
    ... | τ' , wt' , prectyp = τ2 ==> τ' , (SLam (apt1 x₁) (⊑t-wf x₂ x) wt') , PTArr x prectyp
    graduality-syn precctx (PTLam {t = t} prec) (STLam wt)
      with graduality-syn precctx prec wt 
    ... | τ' , wt' , prectyp = ·∀ t τ' , STLam wt' , PTForall prectyp
    graduality-syn precctx (PNEHole prec) (SNEHole wt) 
      with graduality-syn precctx prec wt 
    ... | τ' , wt' , prectyp = ⦇-⦈ , SNEHole wt' , PTHole
    graduality-syn precctx (PAp prec prec₁) (SAp syn match ana) 
      with graduality-syn precctx prec syn
    ... | τ' , wt' , prectyp 
      with ⊑t-▸arr match prectyp 
    ... | τ1' , τ2' , match' , prec1' , prec2' = τ2' , SAp wt' match' (graduality-ana precctx prec1' prec₁ ana) , prec2'
    graduality-syn precctx (PTAp {τ2 = τ2} prec x) (STAp {t = t} x₁ wt x₂ x₃) rewrite (sym x₃) 
      with graduality-syn precctx prec wt 
    ... | τ' , wt' , prectyp 
      with ⊑t-▸forall x₂ prectyp 
    ... | τ'' , match , prec' = Typ[ τ2 / t ] τ'' , STAp (⊑t-wf x₁ x) wt' match refl , ⊑t-Typsubst x prec'
 
  graduality1 : 
    ∀{e e' τ} →     
    (e ⊑ e') →
    (∅ , ∅ ⊢ e => τ) →
    Σ[ τ' ∈ htyp ] ((∅ , ∅ ⊢ e' => τ') × (τ ⊑t τ'))
  graduality1 prec wt = graduality-syn ∅⊑ctx∅ prec wt  

  -- not true
  -- elaboration-specifies : 
  --   ∀{e τ1 τ2 Γ Θ d} →
  --   (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
  --   (τ2 ⊑t τ1)
  -- elaboration-specifies (EALam x x₁ ana) = {!   !}
  -- elaboration-specifies (EATLam x x₁ x₂ ana) = {!   !}
  -- elaboration-specifies (EASubsume x x₁ syn consist) = {!   !}
  -- elaboration-specifies EAEHole = ⊑t-refl
  -- elaboration-specifies (EANEHole x) = ⊑t-refl

  graduality-elab-ana-fun : 
    ∀{e e' τ1 τ2 τ1' τ2' d d' Γ Γ' Θ} →     
    (Γ ⊑ctx Γ') →
    (τ1 ⊑t τ1') →
    (e ⊑ e') →
    (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
    (Θ , Γ' ⊢ e' ⇐ τ1' ~> d' :: τ2') →
    ((Θ , Γ , Γ' ⊢ d ⊑i d') × (τ2 ⊑t τ2'))
  graduality-elab-ana-fun precctx prectyp prec ana (EALam x x₁ ana') = {!   !}
  graduality-elab-ana-fun precctx prectyp prec ana (EATLam x x₁ x₂ ana') = {!   !}
  graduality-elab-ana-fun precctx prectyp prec ana (EASubsume x x₁ x₂ x₃) = {!   !}
  graduality-elab-ana-fun precctx prectyp prec ana EAEHole = PIEHole , {!   !}
  graduality-elab-ana-fun precctx prectyp prec ana (EANEHole x) = {!   !}

  graduality-elab-syn-fun : 
    ∀{e e' τ τ' d d' Γ Γ' Θ} →     
    (Γ ⊑ctx Γ') →
    (e ⊑ e') →
    (Θ , Γ ⊢ e ⇒ τ ~> d) →
    (Θ , Γ' ⊢ e' ⇒ τ' ~> d') →
    ((Θ , Γ , Γ' ⊢ d ⊑i d') × (τ ⊑t τ'))
  graduality-elab-syn-fun = {!   !}
  
  -- mutual 
      
  --   graduality-elab-ana : 
  --     ∀{e e' τ1 τ2 τ1' Γ Γ' Θ d} →     
  --     (Γ ⊑ctx Γ') →
  --     (τ1 ⊑t τ1') →
  --     (e ⊑ e') →
  --     (Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2) →
  --     Σ[ d' ∈ ihexp ] Σ[ τ2' ∈ htyp ] ((Θ , Γ' ⊢ e' ⇐ τ1' ~> d' :: τ2') × (Θ , Γ , Γ' ⊢ d ⊑i d') × (τ2 ⊑t τ2'))
  --   graduality-elab-ana {e' = ⦇-⦈} precctx prectyp prec (EASubsume neq1 neq2 syn consist) with graduality-elab-syn precctx prec syn 
  --   graduality-elab-ana {e' = ⦇-⦈} precctx prectyp prec (EASubsume neq1 neq2 syn consist) | τ' , d' , syn' , prec1 , prec2 
  --     = _ , _ , EAEHole , PIEHole , {!   !}
  --   graduality-elab-ana precctx prectyp prec syn = {!   !}

  --   graduality-elab-syn : 
  --     ∀{e e' Γ Γ' Θ τ d} →     
  --     (Γ ⊑ctx Γ') →
  --     (e ⊑ e') →
  --     (Θ , Γ ⊢ e ⇒ τ ~> d) →
  --     Σ[ τ' ∈ htyp ] Σ[ d' ∈ ihexp ] ((Θ , Γ' ⊢ e' ⇒ τ' ~> d') × (τ ⊑t τ') × (Θ , Γ , Γ' ⊢ d ⊑i d'))
  --   graduality-elab-syn {Γ' = Γ'} {Θ = Θ} precctx (PEHole {u = u}) elab = ⦇-⦈ , ⦇-⦈⟨ ⦇-⦈ ⟩ , ESEHole , PTHole , PIEHole
  --   graduality-elab-syn precctx PConst ESConst = b , c , ESConst , PTBase , PIConst
  --   graduality-elab-syn precctx PVar (ESVar inctx) with ⊑ctx-var inctx precctx
  --   ... | τ' , inctx' , prectyp = _ , _ , ESVar inctx' , prectyp , PIVar
  --   graduality-elab-syn precctx (PAsc prec x) (ESAsc wf ana) with graduality-elab-ana precctx x prec ana 
  --   ... | d' , τ2' , ana' , prec' , prectyp = _ , _ , ESAsc (⊑t-wf wf x) ana' , x , PICast prec' prectyp x
  --   graduality-elab-syn ( precctx , apt1 , apt2 ) (PLam2 prec x) (ESLam apt wf elab) with graduality-elab-syn (⊑ctx-entend ( precctx , apt1 , apt2 ) x) prec elab 
  --   ... | τ' , d' , elab' , prectyp , prec' = _ , _ , ESLam (apt1 apt) (⊑t-wf wf x) elab' , PTArr x prectyp , PILam prec' x
  --   graduality-elab-syn precctx (PTLam prec) (ESTLam elab) with graduality-elab-syn precctx prec elab 
  --   ... | τ' , d' , elab' , prectyp , prec' = _ , _ , ESTLam elab' , PTForall prectyp , PITLam prec'
  --   graduality-elab-syn precctx (PNEHole prec) (ESNEHole elab) with graduality-elab-syn precctx prec elab 
  --   ... | τ' , d' , elab' , prectyp , prec' = _ , _ , ESNEHole elab' , PTHole , PINEHole prec'
  --   graduality-elab-syn precctx (PAp prec1 prec2) (ESAp syn match ana1 ana2) with graduality-syn precctx prec1 syn 
  --   ... | τ1' , syn' , prec1' with ⊑t-▸arr match prec1' 
  --   ... | τ2' , τ' , match' , prec3 , prec4 with graduality-elab-ana precctx (PTArr prec3 prec4) prec1 ana1 
  --   ... | d1' , τ1''' , ana1' , prec5 , prec6 with graduality-elab-ana precctx prec3 prec2 ana2 
  --   ... | d2' , τ2''' , ana2' , prec7 , prec8 = _ , _ , (ESAp syn' match' ana1' ana2') , prec4 , PIAp (PICast prec5 prec6 (PTArr prec3 prec4)) (PICast prec7 prec8 prec3)
  --   graduality-elab-syn precctx (PTAp prec prectyp) (ESTAp wf syn match ana sub) with graduality-syn precctx prec syn 
  --   ... | τ4' , syn' , prec1 with ⊑t-▸forall match prec1 
  --   ... | τ4'' , match' , prec2 with graduality-elab-ana precctx (PTForall prec2) prec ana 
  --   ... | d' , τ2'' , ana' , prec3 , prec4 rewrite (sym sub) = _ , _ , ESTAp (⊑t-wf wf prectyp) syn' match' ana' refl , ⊑t-Typsubst prectyp prec2 , PITAp (PICast prec3 prec4 (PTForall prec2)) prectyp
   
  -- -- not true
  -- -- graduality-boxedval : ∀{d d'} → d boxedval → d ⊑i d' → d' boxedval
  -- -- graduality-boxedval (BVVal val) prec = {!   !}
  -- -- graduality-boxedval (BVArrCast x bv) PIEHole = graduality-boxedval bv PIEHole
  -- -- graduality-boxedval (BVArrCast x bv) (PICast prec x₁ x₂) = {!  bv !}
  -- -- graduality-boxedval (BVForallCast x bv) prec = {!   !}
  -- -- graduality-boxedval (BVHoleCast x bv) prec = {!   !}
 
  -- graduality2 : 
  --   ∀{e e' v} →     
  --   (e ⊑ e') →
  --   (e ⇓ v) → 
  --   Σ[ v' ∈ ihexp ] ((e' ⇓ v') × (∅ , ∅ , ∅ ⊢ v ⊑i v'))
  -- graduality2 prec (Converge elab steps bv) with graduality-elab-syn ∅⊑ctx∅ prec elab 
  -- ... | τ' , d' , elab' , prectyp  , precd with steps 
  -- ... | MSRefl = d' , Converge elab' MSRefl {!   !} , precd 
  -- ... | MSStep x stepsss = {!   !}