open import Nat
open import Prelude
open import core
open typctx
open import contexts
open import weakening

module lemmas-well-formed where 

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
          Θ ⊢ Δ hctxwf → 
          Δ , Θ , Γ ⊢ d :: τ → 
          Θ ⊢ τ wf 
  wf-ta ctxwf hctxwf TAConst = WFBase
  wf-ta (CCtx x₁) hctxwf (TAVar x) = x₁ x
  wf-ta ctxwf hctxwf (TALam x x₁ wt) = WFArr x₁ (wf-ta (merge-tctx-wf ctxwf x₁ x) hctxwf wt)
  wf-ta ctxwf hctxwf (TATLam wt) = WFForall (wf-ta (weaken-tctx-wf ctxwf) (weaken-hctx-wf hctxwf) wt)
  wf-ta ctxwf hctxwf (TAAp wt wt₁) with (wf-ta ctxwf hctxwf wt)
  ... | WFArr wf1 wf2 = wf2
  wf-ta ctxwf hctxwf (TATAp x wt eq) with (wf-ta ctxwf hctxwf wt)
  ... | WFForall wf' rewrite (sym eq) = wf-sub x wf' LTZ
  wf-ta ctxwf (HCtx map) (TAEHole x x₁) with map x 
  ... | (_ , wf) = wf
  wf-ta ctxwf (HCtx map) (TANEHole x wt x₁) with map x 
  ... | (_ , wf) = wf
  wf-ta ctxwf hctxwf (TACast wt x x₁) = x
  wf-ta ctxwf hctxwf (TAFailedCast wt x x₁ x₂) = ground-wf x₁
  
  mutual 

    elab-wf-synth : ∀{Θ Γ e τ d Δ} → 
                      Θ ⊢ Γ tctxwf → 
                      Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ → 
                      Θ ⊢ τ wf 
  -- can probably prove this using typed elaboration.
  --  elab-wf-synth = wf-ta {!!} {!!}
    elab-wf-synth _ ESConst = WFBase
    elab-wf-synth (CCtx wts) (ESVar x) = wts x
    elab-wf-synth ctxwf (ESLam apt x₂ elab) = WFArr x₂ (elab-wf-synth (CCtx (merge-tctx-wf ctxwf x₂ apt)) elab)
    elab-wf-synth ctxwf (ESTLam elab) = WFForall (elab-wf-synth (weaken-tctx-wf ctxwf) elab)
    elab-wf-synth ctxwf (ESAp _ _ _ MAHole _ _) = WFHole
    elab-wf-synth ctxwf (ESAp _ _ wt MAArr _ _) = wf-synth-arr ctxwf wt
    elab-wf-synth ctxwf (ESTAp wf wt _ _ eq) rewrite (sym eq) = wf-sub wf (weaken-t-wf (wf-synth ctxwf wt)) LTZ
    elab-wf-synth _ ESEHole = WFHole
    elab-wf-synth _ (ESNEHole _ _) = WFHole
    elab-wf-synth _ (ESAsc wf _) = wf-ta

    elab-wf-ana : ∀{Γ Θ e τ1 τ2 d Δ} → 
                      Θ ⊢ Γ tctxwf → 
                      Θ ⊢ τ1 wf → 
                      Θ , Γ ⊢ e ⇐ τ1 ~> d :: τ2 ⊣ Δ → 
                      Θ ⊢ τ2 wf 
    elab-wf-ana ctxwf wf1 (EALam apt MAHole wt) = WFArr WFHole (elab-wf-ana (CCtx (merge-tctx-wf ctxwf WFHole apt)) wf1 wt)
    elab-wf-ana ctxwf (WFArr wf1 wf2) (EALam apt MAArr wt) = WFArr wf1 (elab-wf-ana (CCtx (merge-tctx-wf ctxwf wf1 apt)) wf2 wt)
    elab-wf-ana ctxwf wf1 (EASubsume x x₁ wt x₃) = elab-wf-synth ctxwf wt
    elab-wf-ana ctxwf wf1 EAEHole = wf1
    elab-wf-ana ctxwf wf1 (EANEHole x x₁) = wf1

                      
    -- issue : Σ[ Θ ∈ typctx ] Σ[ Γ ∈ tctx ] Σ[ e ∈ hexp ] Σ[ τ ∈ htyp ] Σ[ ctxwf ∈ (Θ ⊢ Γ tctxwf) ] Σ[ twf ∈ (Θ , Γ ⊢ e => τ) ] (Θ ⊢ τ wf → ⊥)
    -- issue =  (record { n = 5 }) , (λ _ → None) , ((·Λ ((⦇-⦈[ 0 ]) ·: (T 5))) < b >) , (T 5) , CCtx (λ ()) , STAp WFBase (STLam (SAsc (WFVar (LTS (LTS (LTS (LTS (LTS LTZ)))))) (ASubsume SEHole TCHole1))) MFForall {!   !} , {!   !}
    
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
  
  