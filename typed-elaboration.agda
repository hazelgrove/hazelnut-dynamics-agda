open import Nat
open import Prelude
open import core
open typctx
open import contexts
open import lemmas-consistency
open import lemmas-disjointness
open import weakening

module typed-elaboration where

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

  mutual 

    typed-elaboration-synth : ∀{Γ e τ d Δ Θ} →
                            Θ ⊢ Γ tctxwf → 
                            Θ , Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Θ , Γ ⊢ d :: τ
    typed-elaboration-synth ctxwf ESConst = TAConst
    typed-elaboration-synth ctxwf (ESVar x₁) = TAVar x₁
    typed-elaboration-synth ctxwf (ESLam apt wf ex) = TALam apt wf (typed-elaboration-synth (merge-tctx-wf ctxwf wf apt) ex)
    typed-elaboration-synth ctxwf (ESTLam ex) = TATLam (typed-elaboration-synth (weaken-tctx-wf ctxwf) ex)
    typed-elaboration-synth ctxwf (ESAp {Δ1 = Δ1} _ d x₁ x₂ x₃ x₄)
      with match-arr-wf (wf-synth ctxwf x₁) x₂
    ... | WFArr wf1 wf2
      with typed-elaboration-ana ctxwf (WFArr wf1 wf2) x₃ | typed-elaboration-ana ctxwf wf1 x₄
    ... | con1 , ih1 | con2 , ih2  = TAAp (TACast (weaken-ta-Δ1 d ih1) (WFArr wf1 wf2) con1) (TACast (weaken-ta-Δ2 {Δ1 = Δ1} d ih2) wf1 con2)
    typed-elaboration-synth ctxwf (ESTAp wf x m ex eq) 
      with match-forall-wf (wf-synth ctxwf x) m
    ... | wf'
      with typed-elaboration-ana ctxwf wf' ex 
    ... | con , ih = TATAp wf (TACast ih wf' con) eq
    typed-elaboration-synth ctxwf (ESEHole {Γ = Γ} {u = u})  = TAEHole (ctx-top ∅ u (Γ , ⦇-⦈) refl)(STAId (λ x τ z → z))
    typed-elaboration-synth ctxwf (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} (d1 , d2) ex)
      with typed-elaboration-synth ctxwf ex
    ... | ih1 = TANEHole {Δ = Δ ,, (u , Γ , ⦇-⦈)} (ctx-top Δ u (Γ , ⦇-⦈) (d2 u (lem-domsingle _ _))) (weaken-ta-Δ1 (d1 , d2) ih1)(STAId (λ x τ₁ z → z))
    typed-elaboration-synth ctxwf (ESAsc wf x)
      with typed-elaboration-ana ctxwf wf x
    ... | con , ih = TACast ih wf con

    typed-elaboration-ana : ∀{Γ e τ τ' d Δ Θ} →
                          Θ ⊢ Γ tctxwf → 
                          Θ ⊢ τ wf → 
                          Θ , Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Θ , Γ ⊢ d :: τ')
    typed-elaboration-ana ctxwf wf (EALam x₁ MAHole ex)
      with typed-elaboration-ana (merge-tctx-wf ctxwf wf x₁) wf ex
    ... | con , D = TCHole1 , TALam x₁ wf D
    typed-elaboration-ana ctxwf (WFArr wf1 wf2) (EALam x₁ MAArr ex)
      with typed-elaboration-ana (merge-tctx-wf ctxwf wf1 x₁) wf2 ex
    ... | con , D = TCArr ~refl con , TALam x₁ wf1 D
    typed-elaboration-ana ctxwf wf (EASubsume x x₁ x₂ x₃) = ~sym x₃ , typed-elaboration-synth ctxwf x₂
    typed-elaboration-ana ctxwf wf (EAEHole {Γ = Γ} {u = u}) = ~refl , TAEHole (ctx-top ∅ u (Γ , _) refl) (STAId (λ x τ z → z))
    typed-elaboration-ana ctxwf wf (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ} (d1 , d2) x)
      with typed-elaboration-synth ctxwf x
    ... | ih1 = ~refl , TANEHole {Δ = Δ ,, (u , Γ , τ)} (ctx-top Δ u (Γ , τ) (d2 u (lem-domsingle _ _)) ) (weaken-ta-Δ1 (d1 , d2) ih1) (STAId (λ x₁ τ₁ z → z))

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