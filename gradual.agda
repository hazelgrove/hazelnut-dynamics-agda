open import Nat
open import Prelude
open import core
open alpha
open import lemmas-alpha
open import lemmas-consistency

open import contexts

-- Note from Thomas: the draft paper is missing a definition of ⊑ for terms

module gradual where

  data _⇓_ : (e : hexp) (v : ihexp) → Set where
    Converge : 
      ∀{e τ d Δ v} → 
      ∅ , ∅ ⊢ e ⇒ τ ~> d ⊣ Δ → 
      d ↦* v → 
      v boxedval →
      e ⇓ v
  
  data _⇑ : (e : hexp) → Set where
    Diverge : 
      ∀{e τ d Δ} → 
      ∅ , ∅ ⊢ e ⇒ τ ~> d ⊣ Δ → 
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
    PEHole : ∀{u e} → e ⊑ ⦇-⦈[ u ]
    PLam1 : ∀{x e1 e2} → e1 ⊑ e2 → (·λ x e1) ⊑ (·λ x e2)
    PLam2 : ∀{x e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑typ τ2 → (·λ x [ τ1 ] e1) ⊑ (·λ x [ τ2 ] e2)
    PTLam : ∀{t e1 e2} → e1 ⊑ e2 → (·Λ t e1) ⊑ (·Λ t e2)
    PNEHole : ∀{u e1 e2} → e1 ⊑ e2 → (⦇⌜ e1 ⌟⦈[ u ]) ⊑ (⦇⌜ e2 ⌟⦈[ u ])
    PAp :  ∀{e1 e2 e3 e4} → e1 ⊑ e3 → e2 ⊑ e4 → (e1 ∘ e2) ⊑ (e3 ∘ e4)
    PTAp : ∀{e1 e2 τ1 τ2} → e1 ⊑ e2 → τ1 ⊑typ τ2 → (e1 < τ1 >) ⊑ (e2 < τ2 >)

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
  ⊑typ-wf (WFForall wf) (PTForall prec) = WFForall (⊑typ-wf wf prec)

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

  apt-lem : ∀{y x τ τ'} → (Γa Γb : tctx) → ((z : Nat) → z # Γa → z # Γb) → y # (Γa ,, (x , τ)) → y # (Γb ,, (x , τ'))
  apt-lem {y = y} Γa Γb apts aptarg with Γa y in eq | Γb y in eq'
  apt-lem {y = y} Γa Γb apts aptarg | None | Some x rewrite (apts y eq) = sym eq'
  apt-lem {y = y} {x = x} Γa Γb apts aptarg | None | None with natEQ x y 
  apt-lem {y = y} Γa Γb apts () | None | None | Inl refl
  ... | Inr x = refl

  -- other-lem : {x z τ τ': Nat} → {τ1 τ2 : htyp} → (Γ Γ' : tctx) → ({y : Nat} {τy τy' : htyp} → (y , τy) ∈ Γ → (y , τy') ∈ Γ' → τy1 ⊑typ τy2) → (x , τ1) ∈ (Γ ,, (z , τ)) → (x , τ2) ∈ (Γ' ,, (z , τ')) → τ1 ⊑typ τ2
  -- other-lem = ?

  ⊑ctx-entend : ∀{Γ x τ Γ' τ'} → (Γ ⊑ctx Γ') → (τ ⊑typ τ') → (Γ ,, (x , τ)) ⊑ctx (Γ' ,, (x , τ'))
  -- ⊑ctx-entend = {!   !}
  ⊑ctx-entend {Γ = Γ} {x = x} {τ = τ} {Γ' = Γ'} {τ' = τ'} ( precctx , apt1 , apt2 ) prectyp = ( {!   !} , (λ {y : Nat} → λ apt → apt-lem Γ Γ' (λ z → apt1) apt) , (λ {y : Nat} → λ apt → apt-lem Γ' Γ (λ z → apt2) apt) ) 
    
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
    graduality-syn {τ = τ} precctx PVar (SVar x) = τ , SVar {!   !} , ⊑typ-refl
    graduality-syn {e' = e' ·: τ'} precctx (PAsc prec x) (SAsc x₁ x₂) = τ' , SAsc (⊑typ-wf x₁ x) (graduality-ana {!   !} x prec x₂) , x
    graduality-syn precctx PEHole wt = ⦇-⦈ , SEHole , PTHole
    graduality-syn precctx (PLam2 prec x) wt = {!   !}
    graduality-syn precctx (PTLam prec) wt = {!   !}
    graduality-syn precctx (PNEHole prec) wt = {!   !}
    graduality-syn precctx (PAp prec prec₁) wt = {!   !}
    graduality-syn precctx (PTAp prec x) wt = {!   !}
 
  graduality1 : 
    ∀{e e' τ} →    
    (e ⊑ e') →
    (∅ , ∅ ⊢ e => τ) →
    Σ[ τ' ∈ htyp ] ((∅ , ∅ ⊢ e' => τ') × (τ ⊑typ τ'))
  graduality1 prec wt = {!   !} 