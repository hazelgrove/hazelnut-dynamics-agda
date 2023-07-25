open import Nat
open import Prelude
open import core
open typctx
open import contexts
open import weakening

module lemmas-well-formed where 

  wf-empty-tctx : ∀{o} -> o ⊢ ∅ tctxwf
  wf-empty-tctx = CCtx (λ ())

  merge-tctx-wf-helper : ∀ {Θ Γ x x' τ τ'} → Θ ⊢ Γ tctxwf → Θ ⊢ τ wf → x # Γ → (x' , τ') ∈ (Γ ,, (x , τ)) → Θ ⊢ τ' wf
  merge-tctx-wf-helper {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf apt h with (natEQ x x') 
  merge-tctx-wf-helper {Γ = Γ} {x = x} {x' = x'} {τ = τ} {τ' = τ'} ctxwf twf apt h | Inl eq rewrite (sym eq) 
    with ctxunicity {Γ = (Γ ,, (x , τ))} {n = x} {t = τ} {t' = τ'} (x∈∪r Γ (■ (x , τ)) x τ (x∈■ x τ) (lem-apart-sing-disj apt)) h 
  ... | eq2 rewrite (sym eq2) = twf
  merge-tctx-wf-helper {Γ = Γ} {τ = τ} (CCtx wfs) twf apt h | Inr n with lem-neq-union-eq {Γ = Γ} {τ = τ} (flip n) h
  ... | map = wfs map

  merge-tctx-wf : ∀ {Θ Γ x τ} → 
                  Θ ⊢ Γ tctxwf → 
                  Θ ⊢ τ wf → 
                  x # Γ →  
                  Θ ⊢ (Γ ,, (x , τ)) tctxwf
  merge-tctx-wf ctxwf wf apt = CCtx (merge-tctx-wf-helper ctxwf wf apt)

  incr-typ-wf : ∀ {Θ t} → Θ ⊢ t wf → [ Θ newtyp] ⊢ incrtyp t wf
  incr-typ-wf = {!   !}

  incr-include : ∀ {Γ x t} → (x , t) ∈ incrtctx Γ → Σ[ t' ∈ htyp ] (((x , t') ∈ Γ) × t == incrtyp t')
  incr-include elem = {!   !} , {!   !} , {!   !}
  
  wf-incr-helper : ∀ {Θ Γ x t} → (∀ {x' t'} → (x' , t') ∈ Γ → Θ ⊢ t' wf) → (x , t) ∈ incrtctx Γ → [ Θ newtyp] ⊢ t wf
  wf-incr-helper {Θ = Θ} {Γ = Γ} map elem with incr-include {Γ = Γ} elem 
  ... | (a , elem2 , eq) rewrite eq = incr-typ-wf (map elem2) 

  wf-incr : ∀ {Θ Γ} → Θ ⊢ Γ tctxwf → [ Θ newtyp] ⊢ incrtctx Γ tctxwf
  wf-incr {Θ = Θ} {Γ = Γ} (CCtx x) = CCtx (wf-incr-helper {Θ = Θ} {Γ = Γ} x)

  wf-sub : ∀ {Θ m τ1 τ2} → Θ ⊢ τ1 wf → [ Θ newtyp] ⊢ τ2 wf → m < (1+ (typctx.n Θ)) → Θ ⊢ Typ[ τ1 / m ] τ2 wf
  wf-sub {τ1 = τ1} {τ2 = b} wf1 wf2 leq = WFBase
  wf-sub {m = m} {τ1 = τ1} {τ2 = T v} wf1 wf2 leq with natEQ m v 
  ... | Inl refl = wf1
  ... | Inr neq with natLT m v 
  wf-sub {m = .Z} {τ1 = τ1} {T .(1+ n)} wf1 (WFVar (LTS x)) leq | Inr neq | Inl (LTZ {n}) = WFVar x
  wf-sub {m = .(1+ m)} {τ1 = τ1} {T .(1+ v)} wf1 (WFVar (LTS x)) leq | Inr neq | Inl (LTS {m} {v} p) = WFVar x
  wf-sub {m = m} {τ1 = τ1} {T v} wf1 (WFVar x) leq | Inr neq | Inr nlt with trichotomy-lemma neq nlt
  ... | lt with lt-lte-is-lt lt leq 
  ... | result = WFVar result
  wf-sub {τ1 = τ1} {τ2 = ⦇-⦈} wf1 wf2 leq = WFHole 
  wf-sub {τ1 = τ1} {τ2 = τ2 ==> τ3} wf1 (WFArr wf2 wf3) leq = WFArr (wf-sub wf1 wf2 leq) (wf-sub wf1 wf3 leq)
  wf-sub {τ1 = τ1} {τ2 = ·∀ τ2} wf1 (WFForall wf2) leq = WFForall (wf-sub (weaken-t-wf wf1) wf2 (LTS leq))


  match-arr-wf : ∀ {Θ τ τ1 τ2} → Θ ⊢ τ wf → τ ▸arr (τ1 ==> τ2) → Θ ⊢ (τ1 ==> τ2) wf
  match-arr-wf wf MAHole = WFArr WFHole WFHole
  match-arr-wf wf MAArr = wf

  match-forall-wf : ∀ {Θ τ τ1} → Θ ⊢ τ wf → τ ▸forall (·∀ τ1) → Θ ⊢ (·∀ τ1) wf
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
    wf-synth ctxwf (SLam apt x₁ wt) = WFArr x₁ (wf-synth (merge-tctx-wf ctxwf x₁ apt) wt)
    wf-synth ctxwf (STLam wt) = WFForall (wf-synth (weaken-tctx-wf ctxwf) wt)
    wf-synth ctxwf (STAp x wt MFHole eq) rewrite (sym eq) = WFHole
    wf-synth ctxwf (STAp x wt MFForall eq) rewrite (sym eq) = wf-sub x (wf-synth-forall ctxwf wt) LTZ
    
    wf-synth-arr : ∀{Θ Γ e τ τ'} → 
                    Θ ⊢ Γ tctxwf → 
                    Θ , Γ ⊢ e => (τ' ==> τ) → 
                    Θ ⊢ τ wf 
    wf-synth-arr ctxwf (SAsc (WFArr _ wf) _) = wf
    wf-synth-arr (CCtx wfs) (SVar x) with (wfs x)
    ... | WFArr _ wf = wf
    wf-synth-arr ctxwf (SAp _ wf MAArr _) with wf-synth-arr ctxwf wf 
    ... | WFArr _ wf = wf
    wf-synth-arr ctxwf (SLam apt wf wt) = wf-synth (merge-tctx-wf ctxwf wf apt) wt
    wf-synth-arr ctxwf (STAp wf wt MFForall eq) with wf-sub wf (wf-synth-forall ctxwf wt) LTZ 
    ... | wf rewrite eq with wf 
    ... | WFArr _ wf  = wf

    wf-synth-forall : ∀{Θ Γ e τ} → 
                      Θ ⊢ Γ tctxwf → 
                      Θ , Γ ⊢ e => (·∀ τ) → 
                      [ Θ newtyp] ⊢ τ wf 
    wf-synth-forall ctxwf (SAsc (WFForall x) x₁) = x
    wf-synth-forall (CCtx wfs) (SVar x) with (wfs x)
    ... | WFForall wf = wf
    wf-synth-forall ctxwf (SAp x wt MAArr x₂) with wf-synth-arr ctxwf wt 
    ... | WFForall wf = wf
    wf-synth-forall ctxwf (STLam wt) = wf-synth (weaken-tctx-wf ctxwf) wt
    wf-synth-forall ctxwf (STAp wf wt MFForall eq) with wf-sub wf (wf-synth-forall ctxwf wt) LTZ
    ... | wf rewrite eq with wf
    ... | WFForall wf = wf

  wf-ta : ∀{Θ Γ d τ Δ} → 
          Θ ⊢ Γ tctxwf → 
          Δ hctxwf → 
          Δ , Θ , Γ ⊢ d :: τ → 
          Θ ⊢ τ wf 
  wf-ta ctxwf hctxwf TAConst = WFBase
  wf-ta (CCtx x₁) hctxwf (TAVar x) = x₁ x
  wf-ta ctxwf hctxwf (TALam x x₁ wt) = WFArr x₁ (wf-ta (merge-tctx-wf ctxwf x₁ x) hctxwf wt)
  wf-ta ctxwf hctxwf (TATLam wt) = WFForall (wf-ta {!   !} hctxwf wt) -- weaken-tctx-wf ctxwf
  wf-ta ctxwf hctxwf (TAAp wt wt₁) with (wf-ta ctxwf hctxwf wt)
  ... | WFArr wf1 wf2 = wf2
  wf-ta ctxwf hctxwf (TATAp x wt eq) with (wf-ta ctxwf hctxwf wt)
  ... | WFForall wf' rewrite (sym eq) = wf-sub x wf' LTZ
  wf-ta ctxwf (HCtx map) (TAEHole x x₁) with map x 
  ... | (_ , wf) = {!   !}
  wf-ta ctxwf (HCtx map) (TANEHole x wt x₁) with map x 
  ... | (_ , wf) = {!   !}
  wf-ta ctxwf hctxwf (TACast wt x x₁) = x
  wf-ta ctxwf hctxwf (TAFailedCast wt x x₁ x₂) = ground-wf x₁
  
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
    elab-wf-synth ctxwf (ESLam apt x₂ elab) = WFArr x₂ (elab-wf-synth (merge-tctx-wf ctxwf x₂ apt) elab)
    elab-wf-synth ctxwf (ESTLam elab) = WFForall (elab-wf-synth (weaken-tctx-wf ctxwf) elab)
    elab-wf-synth ctxwf (ESAp _ _ _ MAHole _ _) = WFHole
    elab-wf-synth ctxwf (ESAp _ _ wt MAArr _ _) = wf-synth-arr ctxwf wt
    elab-wf-synth ctxwf (ESTAp wf wt MFHole wt2 eq) rewrite (sym eq) = WFHole
    elab-wf-synth ctxwf (ESTAp wf wt MFForall wt2 eq) rewrite (sym eq) = wf-sub wf (wf-synth-forall ctxwf wt) LTZ
    elab-wf-synth _ ESEHole = WFHole
    elab-wf-synth _ (ESNEHole _ _) = WFHole
    elab-wf-synth _ (ESAsc wf _) = wf

    elab-wf-ana : ∀{Γ Θ e τ1 τ2 d Δ} → 
                      Θ ⊢ Γ tctxwf → 
                      Θ ⊢ τ1 wf → 
                      Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
                      Θ ⊢ τ2 wf 
    elab-wf-ana ctxwf wf1 (EALam apt MAHole wt) = WFArr WFHole (elab-wf-ana (merge-tctx-wf ctxwf WFHole apt) wf1 wt)
    elab-wf-ana ctxwf (WFArr wf1 wf2) (EALam apt MAArr wt) = WFArr wf1 (elab-wf-ana (merge-tctx-wf ctxwf wf1 apt) wf2 wt)
    elab-wf-ana ctxwf wf1 (EASubsume x x₁ wt x₃) = elab-wf-synth ctxwf wt
    elab-wf-ana ctxwf wf1 (EATLam x₂ x₃ x₄ x₅) = {!   !}
    elab-wf-ana ctxwf wf1 EAEHole = wf1
    elab-wf-ana ctxwf wf1 (EANEHole x x₁) = wf1