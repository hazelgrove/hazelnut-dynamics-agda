open import Nat
open import Prelude
open import core
open import contexts
open import weakening
open import contraction
open import exchange
open import rewrite-util

module lemmas-well-formed where 

  wf-empty-tctx : ∀{o} -> o ⊢ ∅ tctxwf
  wf-empty-tctx = CCtx (λ ())

  some-inj : ∀ {A : Set} (y y' : A) → Some y' == Some y → y' == y 
  some-inj y y' refl = refl 
  
  merge-wf-helper : ∀ {Θ Γ1 Γ2 x y} → 
    Θ ⊢ Γ1 tctxwf → 
    Θ ⊢ Γ2 tctxwf → 
    (x , y) ∈ (Γ1 ∪ Γ2) → 
    Θ ⊢ y wf
  merge-wf-helper {Γ1 = Γ1} {Γ2 = Γ2} {x = x} {y = y} wf1 wf2 elem with (Γ1 x) in thing
  merge-wf-helper {Γ1 = Γ1} {Γ2 = Γ2} {x = x} {y = y} (CCtx map1) wf2 elem | Some y' rewrite (some-inj y y' elem) = map1 thing
  merge-wf-helper {Γ1 = Γ1} {Γ2 = Γ2} {x = x} {y = y} wf1 (CCtx map2) elem | None = map2 elem

  merge-wf : ∀ {Θ Γ1 Γ2} → 
    Θ ⊢ Γ1 tctxwf → 
    Θ ⊢ Γ2 tctxwf → 
    Θ ⊢ (Γ1 ∪ Γ2) tctxwf
  merge-wf wf1 wf2 = CCtx λ x → merge-wf-helper wf1 wf2 x

  singelton-wf-helper : ∀ {Θ x x' y y'} → Θ ⊢ y wf → (x' , y') ∈ (■ (x , y)) → Θ ⊢ y' wf
  singelton-wf-helper wf elem rewrite lem-insingeq elem = wf

  singelton-wf : ∀ {Θ x τ} → Θ ⊢ τ wf → Θ ⊢ ■ (x , τ) tctxwf
  singelton-wf wf = CCtx λ x → singelton-wf-helper wf x

  merge-tctx-wf : ∀ {Θ Γ x τ} → 
                  Θ ⊢ Γ tctxwf → 
                  Θ ⊢ τ wf → 
                  Θ ⊢ (Γ ,, (x , τ)) tctxwf
  merge-tctx-wf ctxwf wf = merge-wf ctxwf (singelton-wf wf)

  strengthening : ∀ {A} → ∀ {Γ : A ctx} → ∀ {x τ x' τ'} → (x , τ) ∈ (Γ ,, (x' , τ')) → (x == x' → ⊥) → (x , τ) ∈ Γ
  strengthening {Γ = Γ} {x = x} {x' = x'} elem neq with (Γ x)
  ... | Some _ = elem
  ... | None  with natEQ x' x 
  ... | Inl refl = abort (neq refl)
  ... | Inr neq = elem

  lem-subctx-extend : (Γ Γ' : ⊤ ctx) (x : Nat) → ((x' : Nat) → (x' , <>) ∈ Γ → (x' , <>) ∈ Γ') →
    ((x' : Nat) → (x' , <>) ∈ (Γ ,, (x , <>)) → (x' , <>) ∈ (Γ' ,, (x , <>)))
  lem-subctx-extend Γ Γ' x cond x' mem with ctxindirect Γ x'
  ... | Inl (<> , inl) rewrite inl rewrite ! (someinj mem) rewrite cond x' inl = refl
  ... | Inr nil rewrite nil with natEQ x x'
  ...   | Inr neq = abort (somenotnone (! mem))
  ...   | Inl refl with Γ' x'
  ...     | Some <> = refl
  ...     | None rewrite natEQrefl {x'} = refl

  wf-weaken-gen : ∀{τ Θ Θ'} → ((t : Nat) → (t , <>) ∈ Θ → (t , <>) ∈ Θ') → Θ ⊢ τ wf → Θ' ⊢ τ wf
  wf-weaken-gen cond (WFVar {a = a} x) = WFVar (cond a x)
  wf-weaken-gen cond WFBase = WFBase
  wf-weaken-gen cond WFHole = WFHole
  wf-weaken-gen cond (WFArr wf wf₁) = WFArr (wf-weaken-gen cond wf) (wf-weaken-gen cond wf₁)
  wf-weaken-gen {Θ = Θ} {Θ' = Θ'} cond (WFForall {n = n} wf) = WFForall (wf-weaken-gen (lem-subctx-extend Θ Θ' n cond) wf)

  wf-closed : ∀{τ Θ} → ∅ ⊢ τ wf → Θ ⊢ τ wf
  wf-closed = wf-weaken-gen (λ t mem → abort (somenotnone (! mem)))

  wf-sub : ∀ {Θ t τ1 τ2 τ3} → Θ ⊢ τ1 wf → (Θ ,, (t , <>)) ⊢ τ3 wf → τ2 == ·∀ t τ3 → Θ ⊢ Typ[ τ1 / t ] τ3 wf
  wf-sub {τ3 = b} wf1 wf2 eq = WFBase
  wf-sub {Θ} {t = t} {τ3 = T x} wf1 (WFVar {a = a} p) eq with natEQ t x
  ... | Inl refl = wf1
  ... | Inr neq with ctxindirect Θ x
  ...   | Inl (<> , inctx) = WFVar inctx
  ...   | Inr ninctx rewrite ninctx rewrite natEQneq neq rewrite natEQneq neq = WFVar (abort (somenotnone (! p)))
  wf-sub {τ3 = ⦇-⦈} wf1 wf2 eq = WFHole
  wf-sub {τ3 = τ4 ==> τ5} wf1 (WFArr wf2 wf3) eq rewrite eq = WFArr (wf-sub wf1 wf2 refl) (wf-sub wf1 wf3 refl)
  wf-sub {Θ} {t = t} {τ1} {τ2} {τ3} wf1 (WFForall {n = n} {t = τ4} wf2) eq with natEQ t n
  ... | Inl refl = WFForall (wf-contraction {Θ} {n} wf2)
  ... | Inr neq  = WFForall (wf-sub (weaken-t-wf wf1) (exchange-wf {t} {n} {τ4} {Θ} wf2) refl)

  wf-tfresht : ∀{Θ t τ} -> tfresht t τ -> (Θ ,, (t , <>)) ⊢ τ wf -> Θ ⊢ τ wf
  wf-tfresht {Θ} {t'} (TFTVar {t = t} ne) (WFVar x) with ctxindirect Θ t
  ... | Inl (<> , int) = WFVar int
  ... | Inr nint rewrite nint with natEQ t' t
  ...   | Inl refl = abort (ne refl)
  ...   | Inr neq = abort (somenotnone (! x))
  wf-tfresht tf WFBase = WFBase
  wf-tfresht tf WFHole = WFHole
  wf-tfresht (TFArr tf1 tf2) (WFArr wf1 wf2) = WFArr (wf-tfresht tf1 wf1) (wf-tfresht tf2 wf2)
  wf-tfresht {Θ} (TFForall x tf) (WFForall wf) = WFForall (wf-tfresht tf (rewrite-t-wf (exchange-Θ {Θ = Θ}) wf))
  match-arr-wf : ∀ {Θ τ τ1 τ2} → Θ ⊢ τ wf → τ ▸arr (τ1 ==> τ2) → Θ ⊢ (τ1 ==> τ2) wf
  match-arr-wf wf MAHole = WFArr WFHole WFHole
  match-arr-wf wf MAArr = wf

  match-forall-wf : ∀ {Θ τ t τ1} → Θ ⊢ τ wf → τ ▸forall (·∀ t τ1) → Θ ⊢ (·∀ t τ1) wf
  match-forall-wf wf MFHole = WFForall WFHole 
  match-forall-wf wf MFForall = wf

  ground-wf : ∀ {Θ τ} → τ ground → Θ ⊢ τ wf
  ground-wf GBase = WFBase
  ground-wf GArr = WFArr WFHole WFHole
  ground-wf GForall = WFForall WFHole

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
    wf-synth ctxwf (SLam apt x₁ wt) = WFArr x₁ (wf-synth (merge-tctx-wf ctxwf x₁) wt)
    wf-synth ctxwf (STLam wt) = WFForall (wf-synth (weaken-tctx-wf ctxwf) wt)
    wf-synth ctxwf (STAp x wt MFHole eq) rewrite (sym eq) = WFHole
    wf-synth ctxwf (STAp x wt MFForall eq) rewrite (sym eq) = wf-sub x (wf-synth-forall ctxwf wt) refl
    
    wf-synth-arr : ∀{Θ Γ e τ τ'} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ , Γ ⊢ e => (τ' ==> τ) → 
                    Θ ⊢ τ wf 
    wf-synth-arr ctxwf (SAsc (WFArr _ wf) _) = wf
    wf-synth-arr (CCtx wfs) (SVar x) with (wfs x)
    ... | WFArr _ wf = wf
    wf-synth-arr ctxwf (SAp _ wf MAArr _) with wf-synth-arr ctxwf wf 
    ... | WFArr _ wf = wf
    wf-synth-arr ctxwf (SLam apt wf wt) = wf-synth (merge-tctx-wf ctxwf wf) wt
    wf-synth-arr ctxwf (STAp wf wt MFForall eq)  with wf-sub wf (wf-synth-forall ctxwf wt) refl
    ... | wf rewrite eq with wf 
    ... | WFArr _ wf  = wf

    wf-synth-forall : ∀{Θ Γ e t τ} → 
                      Θ ⊢ Γ tctxwf → 
                      Θ , Γ ⊢ e => (·∀ t τ) → 
                      (Θ ,, (t , <>)) ⊢ τ wf 
    wf-synth-forall ctxwf (SAsc (WFForall x) x₁) = x
    wf-synth-forall (CCtx wfs) (SVar x) with (wfs x)
    ... | WFForall wf = wf
    wf-synth-forall ctxwf (SAp x wt MAArr x₂) with wf-synth-arr ctxwf wt 
    ... | WFForall wf = wf
    wf-synth-forall ctxwf (STLam wt) = wf-synth (weaken-tctx-wf ctxwf) wt
    wf-synth-forall ctxwf (STAp wf wt MFForall eq) with wf-sub wf (wf-synth-forall ctxwf wt) refl
    ... | wf rewrite eq with wf
    ... | WFForall wf = wf
  
  mutual 

    elab-wf-synth : ∀{Θ Γ e τ d Δ} → 
                      Θ ⊢ Γ tctxwf → 
                      Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ → 
                      Θ ⊢ τ wf 
  -- A: can probably prove this using typed elaboration.
  -- T: but typed-elaboration currently depends on theorems in this file, and no circ dependencies
  -- T: this could be avoided by separating the theorems but I think these should stay together
    elab-wf-synth _ ESConst = WFBase
    elab-wf-synth (CCtx wts) (ESVar x) = wts x
    elab-wf-synth ctxwf (ESLam apt x₂ elab) = WFArr x₂ (elab-wf-synth (merge-tctx-wf ctxwf x₂) elab)
    elab-wf-synth ctxwf (ESTLam elab) = WFForall (elab-wf-synth (weaken-tctx-wf ctxwf) elab)
    elab-wf-synth ctxwf (ESAp _ _ _ MAHole _ _) = WFHole
    elab-wf-synth ctxwf (ESAp _ _ wt MAArr _ _) = wf-synth-arr ctxwf wt
    elab-wf-synth ctxwf (ESTAp wf wt MFHole wt2 eq) rewrite (sym eq) = WFHole
    elab-wf-synth ctxwf (ESTAp wf wt MFForall wt2 eq) rewrite (sym eq) = wf-sub wf (wf-synth-forall ctxwf wt) refl
    elab-wf-synth _ ESEHole = WFHole
    elab-wf-synth _ (ESNEHole _ _) = WFHole
    elab-wf-synth _ (ESAsc wf _) = wf

    elab-wf-ana : ∀{Γ Θ e τ1 τ2 d Δ} → 
                      Θ ⊢ Γ tctxwf → 
                      Θ ⊢ τ1 wf → 
                      Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
                      Θ ⊢ τ2 wf 
    elab-wf-ana ctxwf wf1 (EALam apt MAHole wt) = WFArr WFHole (elab-wf-ana (merge-tctx-wf ctxwf WFHole) wf1 wt)
    elab-wf-ana ctxwf (WFArr wf1 wf2) (EALam apt MAArr wt) = WFArr wf1 (elab-wf-ana (merge-tctx-wf ctxwf wf1) wf2 wt)
    elab-wf-ana ctxwf wf1 (EASubsume x x₁ wt x₃) = elab-wf-synth ctxwf wt
    elab-wf-ana ctxwf wf1 (EATLam x₂ x₃ m wf2) with match-forall-wf wf1 m
    ... | WFForall wf3 = WFForall (elab-wf-ana (weaken-tctx-wf ctxwf) wf3 wf2)
    elab-wf-ana ctxwf wf1 EAEHole = wf1
    elab-wf-ana ctxwf wf1 (EANEHole x x₁) = wf1

  mutual 

    typsub-wf : ∀ {Θ t τ τ' τ''} →
      (Θ ,, (t , <>)) ⊢ τ wf →
      Θ ⊢ τ' wf →
      τ'' == Typ[ τ' / t ] τ →
      Θ ⊢ τ'' wf
    typsub-wf {τ = b} wf1 wf2 eq rewrite eq = WFBase
    typsub-wf {t = t} {τ = T x} wf1 wf2 eq with natEQ t x 
    ... | Inl refl rewrite eq = wf2
    typsub-wf {Θ = Θ} {t = t} {T x} (WFVar elem) wf2 eq | Inr neq rewrite eq = WFVar (strengthening {Γ = Θ} elem (flip neq))
    typsub-wf {τ = ⦇-⦈} wf1 wf2 eq rewrite eq = WFHole
    typsub-wf {τ = τ ==> τ₁} (WFArr wf1 wf1') wf2 eq rewrite eq = WFArr (typsub-wf wf1 wf2 refl) (typsub-wf wf1' wf2 refl)
    typsub-wf {Θ = Θ} {t = t1} {τ = ·∀ t2 τ} (WFForall wf1) wf2 eq with natEQ t1 t2
    ... | Inl refl rewrite eq rewrite (contract {x = t2} {τ = <>} Θ) = WFForall wf1
    ... | Inr neq rewrite eq rewrite (swap {x = t1} {y = t2} {τ1 = <>} {τ2 = <>} Θ neq) = WFForall (typsub-wf wf1 (weaken-t-wf wf2) refl) 


    typenv-wf : ∀ {Δ Θ Γ θ σ Θ' Γ' τ τ'} →
      Δ hctxwf →
      Θ ⊢ Γ tctxwf →
      Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ' →
      Θ' ⊢ Γ' tctxwf →
      Θ' ⊢ τ wf →
      τ' == apply-typenv θ τ →
      Θ ⊢ τ' wf
    typenv-wf hctxwf ctxwf1 (STAIdId x₁ x₂) ctxwf2 wf eq rewrite eq = x₂ _ wf
    typenv-wf hctxwf ctxwf1 (STAIdSubst sub x) ctxwf2 wf eq =
      typenv-wf hctxwf ctxwf3 sub ctxwf2 wf eq 
      where 
      ctxwf3 = merge-tctx-wf ctxwf1 (wf-ta ctxwf1 hctxwf x)
    typenv-wf {Θ = Θ} {θ = θ} {τ = τ} hctxwf ctxwf1 (STASubst {y = y} sub x) ctxwf2 wf eq =
      typsub-wf wf2 (wf-closed x) eq
      where 
      wf2 = typenv-wf hctxwf (weaken-tctx-wf ctxwf1) sub ctxwf2 wf refl

    -- Should hold since everything in θ is closed
    wf-ty-subst : ∀{Δ Θ Θ' Γ Γ' Γ'' θ σ} →
      Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ'' →
      Γ'' == apply-typenv-env θ Γ' →
      Θ' ⊢ Γ' tctxwf →
      Θ' ⊢ Γ'' tctxwf
    wf-ty-subst = {!   !}

    wf-ta : ∀{Θ Γ d τ Δ} → 
            Θ ⊢ Γ tctxwf → 
            Δ hctxwf →
            Δ , Θ , Γ ⊢ d :: τ → 
            Θ ⊢ τ wf 
    wf-ta ctxwf hctwwf TAConst = WFBase
    wf-ta (CCtx x₁) hctwwf (TAVar x) = x₁ x
    wf-ta ctxwf hctwwf (TALam x x₁ wt) = WFArr x₁ (wf-ta (merge-tctx-wf ctxwf x₁) hctwwf wt)
    wf-ta ctxwf hctwwf (TATLam apt wt) = WFForall (wf-ta (weaken-tctx-wf ctxwf) hctwwf wt)
    wf-ta ctxwf hctwwf (TAAp wt wt₁ alpha) with (wf-ta ctxwf hctwwf wt)
    ... | WFArr wf1 wf2 = wf2
    wf-ta ctxwf hctwwf (TATAp x wt eq) with (wf-ta ctxwf hctwwf wt)
    ... | WFForall wf' rewrite (sym eq) = wf-sub x wf' refl
    wf-ta ctxwf (HCtx map) (TAEHole x x₁ eq eq') with map x 
    ... | (thing1 , thing2) = typenv-wf (HCtx map) ctxwf x₁ (wf-ty-subst x₁ eq' thing1) thing2 eq
    wf-ta ctxwf (HCtx map) (TANEHole x wt x₁ eq eq') with map x 
    ... | (thing1 , thing2) = typenv-wf (HCtx map) ctxwf x₁ (wf-ty-subst x₁ eq' thing1) thing2 eq
    wf-ta ctxwf hctwwf (TACast wt x x₁ alpha) = x
    wf-ta ctxwf hctwwf (TAFailedCast wt x x₁ x₂ _) = ground-wf x₁

  
    no-tvar-casts : ∀{ Γ n τ d Δ} → ∅ ⊢ Γ tctxwf → Δ hctxwf → Δ , ∅ , Γ ⊢ d ⟨ T n ⇒ ⦇-⦈ ⟩ :: τ → ⊥
    no-tvar-casts ctxwf hctxwf (TACast wt x x₁ alpha) with wf-ta ctxwf hctxwf wt 
    ... | WFVar () 


  ~closed : ∀{τ τ'} → ∅ ⊢ τ wf → τ ~ τ' → ∅ ⊢ τ' wf
  ~closed wf consis = {!   !}
