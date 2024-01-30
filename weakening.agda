{-# OPTIONS --allow-unsolved-metas #-}
open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-disjointness
open import exchange
open import rewrite-util
open import lemmas-alpha

-- this module contains all the proofs of different weakening structural
-- properties that we use for the hypothetical judgements
module weakening where
  weaken-t-wf : ∀ {Θ x τ} → tunboundt-in x τ → Θ ⊢ τ wf → (Θ ,, (x , <>)) ⊢ τ wf
  weaken-t-wf {Θ} _ (WFVar x) = WFVar (x∈∪l Θ _ _ <> x)
  weaken-t-wf _ WFBase = WFBase
  weaken-t-wf _ WFHole = WFHole
  weaken-t-wf (UBArr ub ub₁) (WFArr wf wf₁) = WFArr (weaken-t-wf ub wf) (weaken-t-wf ub₁ wf₁)
  weaken-t-wf {Θ} (UBForall x ub) (WFForall apt wf) = WFForall (lem-apart-extend {Γ = Θ} apt (flip x)) (exchange-wf {Θ = Θ} (weaken-t-wf ub wf))

  lem-subctx-extend : (Γ Γ' : ⊤ ctx) (x : Nat) → ((x' : Nat) → (x' , <>) ∈ Γ → (x' , <>) ∈ Γ') →
    ((x' : Nat) → (x' , <>) ∈ (Γ ,, (x , <>)) → (x' , <>) ∈ (Γ' ,, (x , <>)))
  lem-subctx-extend Γ Γ' x cond x' mem with ctxindirect Γ x'
  ... | Inl (<> , inl) rewrite inl rewrite ! (someinj mem) rewrite cond x' inl = refl
  ... | Inr nil rewrite nil with natEQ x x'
  ...   | Inr neq = abort (somenotnone (! mem))
  ...   | Inl refl with Γ' x'
  ...     | Some <> = refl
  ...     | None rewrite natEQrefl {x'} = refl
  {-
  weaken-t-wf' : ∀{τ Θ Θ'} → ((t : Nat) → (t , <>) ∈ Θ → (t , <>) ∈ Θ') → Θ ⊢ τ wf → Θ' ⊢ τ wf
  weaken-t-wf' cond (WFVar {a = a} x) = WFVar (cond a x)
  weaken-t-wf' cond WFBase = WFBase
  weaken-t-wf' cond WFHole = WFHole
  weaken-t-wf' cond (WFArr wf wf₁) = WFArr (weaken-t-wf' cond wf) (weaken-t-wf' cond wf₁)
  weaken-t-wf' {Θ = Θ} {Θ' = Θ'} cond (WFForall {n = n} apt wf) = WFForall {!   !} (weaken-t-wf' (lem-subctx-extend Θ Θ' n cond) wf)
  -}
  {-with natEQ x y
  ... | Inl refl = WFForall (abort (ne refl)) 
  ... | Inr neq = WFForall (exchange-wf {y} {x} {t} {Θ} (flip neq) {! wf  !})
  -}

  weaken-tctx-wf : ∀ {Θ Γ x} → Θ ⊢ Γ tctxwf → (Θ ,, (x , <>)) ⊢ Γ tctxwf
  weaken-tctx-wf (CCtx x) = CCtx (λ x₁ → weaken-t-wf {!   !} (x x₁))

{-
  weaken-hctx-wf : ∀ {Θ Δ x} → Θ ⊢ Δ hctxwf → (Θ ,, (x , <>)) ⊢ Δ hctxwf
  weaken-hctx-wf (HCtx map) = 
    HCtx (λ key → 
      (let (p1 , p2) = (map key) in 
      (weaken-tctx-wf p1) , (weaken-t-wf p2)))
-}

  mutual
    weaken-subst-Δ : ∀{Δ1 Δ2 Γ θ σ Γ' Θ Θ'} → Δ1 ## Δ2
                                     → Δ1 , Θ , Γ ⊢ θ , σ :s: Θ' , Γ'
                                     → (Δ1 ∪ Δ2) , Θ , Γ ⊢ θ , σ :s: Θ' , Γ'
    weaken-subst-Δ disj (STAIdId x₁ x₂) = STAIdId x₁ x₂
    weaken-subst-Δ disj (STAIdSubst subst x alpha) = STAIdSubst (weaken-subst-Δ disj subst) (weaken-ta-Δ1 disj x) alpha
    weaken-subst-Δ disj (STASubst subst x) = STASubst (weaken-subst-Δ disj subst) x

    weaken-ta-Δ1 : ∀{Δ1 Δ2 Γ d τ Θ} → Δ1 ## Δ2
                                  → Δ1 , Θ , Γ ⊢ d :: τ
                                  → (Δ1 ∪ Δ2) , Θ , Γ ⊢ d :: τ
    weaken-ta-Δ1 disj TAConst = TAConst
    weaken-ta-Δ1 disj (TAVar x₁) = TAVar x₁
    weaken-ta-Δ1 disj (TALam x₁ wf wt) = TALam x₁ wf (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TATLam apt wt) = TATLam apt (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TAAp wt wt₁ alpha) = TAAp (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁) alpha
    weaken-ta-Δ1 disj (TATAp wf wt eq) = TATAp wf (weaken-ta-Δ1 disj wt) eq
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TAEHole {u = u} {Γ' = Γ'} x x₁ eq eq') = TAEHole (x∈∪l Δ1 Δ2 u _ x ) (weaken-subst-Δ disj x₁) eq eq'
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TANEHole {u = u} {Γ' = Γ'} x wt x₁ eq eq') = TANEHole (x∈∪l Δ1 Δ2 u _ x) (weaken-ta-Δ1 disj wt) (weaken-subst-Δ disj x₁) eq eq'
    weaken-ta-Δ1 disj (TACast wt wf x alpha) = TACast (weaken-ta-Δ1 disj wt) wf x alpha
    weaken-ta-Δ1 disj (TAFailedCast wt x x₁ x₂ alpha) = TAFailedCast (weaken-ta-Δ1 disj wt) x x₁ x₂ alpha

  -- this is a little bit of a time saver. since ∪ is commutative on
  -- disjoint contexts, and we need that premise anyway in both positions,
  -- there's no real reason to repeat the inductive argument above
  weaken-ta-Δ2 : ∀{Δ1 Δ2 Γ d τ Θ} → Δ1 ## Δ2
                                → Δ2 , Θ , Γ ⊢ d :: τ
                                → (Δ1 ∪ Δ2) , Θ , Γ ⊢ d :: τ
  weaken-ta-Δ2 {Δ1} {Δ2} {Γ} {d} {τ} {Θ} disj D = tr (λ q → q , Θ , Γ ⊢ d :: τ) (∪comm Δ2 Δ1 (##-comm disj)) (weaken-ta-Δ1 (##-comm disj) D)


  -- note that these statements are somewhat stronger than usual. this is
  -- because we don't have implcit α-conversion. this reifies the
  -- often-silent on paper assumption that if you collide with a bound
  -- variable you can just α-convert it away and not worry.
  mutual
    weaken-synth : ∀{ x Γ e τ τ' Θ} → freshh x e
                                  → Θ , Γ ⊢ e => τ
                                  → Θ , (Γ ,, (x , τ')) ⊢ e => τ
    weaken-synth FRHConst SConst = SConst
    weaken-synth (FRHAsc frsh) (SAsc wf x₁) = SAsc wf (weaken-ana frsh x₁)
    weaken-synth {Γ = Γ} (FRHVar {x = x} x₁) (SVar {x = y} x₂) = SVar (x∈∪l Γ (■(x , _)) y _  x₂)
    weaken-synth {Γ = Γ} (FRHLam2 x₁ frsh) (SLam x₂ wf wt) =
                    SLam (apart-extend1 Γ (flip x₁) x₂) wf
                         (exchange-synth {Γ = Γ} (flip x₁) ((weaken-synth frsh wt)))
    weaken-synth (FRHTLam x) (STLam x₂) = STLam (weaken-synth x x₂)
    weaken-synth FRHEHole SEHole = SEHole
    weaken-synth (FRHNEHole frsh) (SNEHole x₁ wt) = SNEHole x₁ (weaken-synth frsh wt)
    weaken-synth (FRHAp frsh frsh₁) (SAp x₁ wt x₂ x₃) = SAp x₁ (weaken-synth frsh wt) x₂ (weaken-ana frsh₁ x₃)
    weaken-synth (FRHTAp x₁) (STAp wf x₂ x₃ eq) = STAp wf (weaken-synth x₁ x₂) x₃ eq

    weaken-ana : ∀{x Γ e τ τ' Θ} → freshh x e
                               → Θ , Γ ⊢ e <= τ
                               → Θ , (Γ ,, (x , τ')) ⊢ e <= τ
    weaken-ana frsh (ASubsume x₁ x₂) = ASubsume (weaken-synth frsh x₁) x₂
    weaken-ana {Γ = Γ} (FRHLam1 neq frsh) (ALam x₂ x₃ wt) =
                     ALam (apart-extend1 Γ (flip neq) x₂)
                          x₃
                          (exchange-ana {Γ = Γ} (flip neq) (weaken-ana frsh wt))
    weaken-ana (FRHTLam x₁) (ATLam x₂ x₃) = ATLam x₂ (weaken-ana x₁ x₃)

  mutual
    weaken-subst-Γ : ∀{ x Γ Δ θ σ Γ' τ Θ Θ'} →
                     envfresh x σ →
                     Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ' →
                     Δ , Θ , (Γ ,, (x , τ)) ⊢ θ , σ :s: Θ' , Γ'
    weaken-subst-Γ {Γ = Γ} (EFId x₁) (STAIdId x₂ prem) = STAIdId (λ x τ x₃ → x∈∪l Γ _ x τ (x₂ x τ x₃) ) prem
    weaken-subst-Γ {x = x} {Γ = Γ} (EFSubst x₁ efrsh x₂) (STAIdSubst {y = y} {τ = τ'} subst x₃ alpha) =
      STAIdSubst (exchange-subst-Γ {Γ = Γ} (flip x₂) (weaken-subst-Γ {Γ = Γ ,, (y , τ')} efrsh {!   !}))
               (weaken-ta x₁ x₃) alpha
    weaken-subst-Γ (EFId x) (STASubst x₁ x₂) = STASubst (weaken-subst-Γ (EFId x) x₁) x₂
    weaken-subst-Γ {x = x} {Γ = Γ} (EFSubst x₁ efrsh x₂) (STASubst {y = y} {τ = τ'} subst x₃) =
      STASubst (weaken-subst-Γ ((EFSubst x₁ efrsh x₂)) subst) x₃ 
    

    weaken-ta : ∀{x Γ Δ d τ τ' Θ} →
                fresh x d →
                Δ , Θ , Γ ⊢ d :: τ →
                Δ , Θ , Γ ,, (x , τ') ⊢ d :: τ
    weaken-ta _ TAConst = TAConst
    weaken-ta {x} {Γ} {_} {_} {τ} {τ'} (FVar x₂) (TAVar x₃) = TAVar (x∈∪l Γ (■ (x , τ')) _ _ x₃)
    weaken-ta {x = x} frsh (TALam {x = y} apt wf wt) with natEQ x y
    weaken-ta (FLam x₁ x₂) (TALam apt wf wt) | Inl refl = abort (x₁ refl)
    weaken-ta {Γ = Γ} {τ' = τ'} (FLam x₁ x₃) (TALam {x = y} x₄ wf wt) | Inr x₂ = TALam (apart-extend1 Γ (flip x₁) x₄) wf (exchange-ta-Γ {Γ = Γ} (flip x₁) (weaken-ta x₃ wt))
    weaken-ta {x} {Γ} {τ' = τ'} (FTLam frsh) (TATLam apt x₁) = TATLam apt (weaken-ta frsh x₁)
    weaken-ta (FAp frsh frsh₁) (TAAp wt wt₁ alpha) = TAAp (weaken-ta frsh wt) (weaken-ta frsh₁ wt₁) alpha
    weaken-ta (FTAp frsh) (TATAp wf x₁ eq) = TATAp wf (weaken-ta frsh x₁) eq
    weaken-ta (FHole x₁) (TAEHole x₂ x₃ eq eq') = TAEHole x₂ (weaken-subst-Γ x₁ x₃) eq eq'
    weaken-ta (FNEHole x₁ frsh) (TANEHole x₂ wt x₃ eq eq') = TANEHole x₂ (weaken-ta frsh wt) (weaken-subst-Γ x₁ x₃) eq eq'
    weaken-ta (FCast frsh) (TACast wt wf x₁ alpha) = TACast (weaken-ta frsh wt) wf x₁ alpha
    weaken-ta (FFailedCast frsh) (TAFailedCast wt x₁ x₂ x₃ alpha) = TAFailedCast (weaken-ta frsh wt) x₁ x₂ x₃ alpha

  mutual 
    weaken-subst-Θ : ∀{Γ Δ θ t σ Γ' Θ Θ'} →
                     tunbound-in-θ t θ →
                     tunbound-in-σ t σ →
                     Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ' →
                     Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ'
    weaken-subst-Θ {Θ = Θ} UBθId ubs (STAIdId x p) = STAIdId x λ t x₁ → let p' = p t x₁ in lem-dom-extend {Γ = Θ} p'
    weaken-subst-Θ ub (TUBσSubst x₂ ubs) (STAIdSubst x x₁ alpha) = STAIdSubst (weaken-subst-Θ ub ubs x) (weaken-ta-typ x₂ x₁) alpha
    weaken-subst-Θ {Θ = Θ} (UBθSubst x₂ ub) ubs (STASubst x x₁) = STASubst (rewrite-theta-subst (exchange-Θ {Θ = Θ}) (weaken-subst-Θ ub ubs x)) x₁

    weaken-ta-typ : ∀{Γ Δ Θ d t τ} →
                  tunbound-in t d →
                  Δ , Θ , Γ ⊢ d :: τ →
                  Δ , (Θ ,, (t , <>)) , Γ ⊢ d :: τ
    weaken-ta-typ ub TAConst = TAConst
    weaken-ta-typ ub (TAVar x) = TAVar x
    weaken-ta-typ (TUBLam2 ub x₂) (TALam x x₁ ta) = TALam x (weaken-t-wf x₂ x₁) (weaken-ta-typ ub ta)
    weaken-ta-typ {Θ = Θ} (TUBTLam x₁ ub) (TATLam x ta) = TATLam (lem-apart-extend {Γ = Θ} x (flip x₁)) (rewrite-theta (exchange-Θ {Θ = Θ}) (weaken-ta-typ ub ta))
    weaken-ta-typ (TUBAp ub ub₁) (TAAp ta ta₁ alpha) = TAAp (weaken-ta-typ ub ta) (weaken-ta-typ ub₁ ta₁) alpha
    weaken-ta-typ (TUBTAp ub x₂) (TATAp x ta x₁) = TATAp (weaken-t-wf x₂ x) (weaken-ta-typ ub ta) x₁
    weaken-ta-typ (TUBHole x₄ x₅) (TAEHole x x₁ x₂ x₃) = TAEHole x (weaken-subst-Θ x₄ x₅ x₁) x₂ x₃
    weaken-ta-typ (TUBNEHole x₄ x₅ ub) (TANEHole x ta x₁ x₂ x₃) = TANEHole x (weaken-ta-typ ub ta) (weaken-subst-Θ x₄ x₅ x₁) x₂ x₃
    weaken-ta-typ (TUBCast ub x₂ x₃) (TACast ta x x₁ alpha) = TACast (weaken-ta-typ ub ta) (weaken-t-wf x₃ x) x₁ alpha
    weaken-ta-typ (TUBFailedCast ub x₃ x₄) (TAFailedCast ta x x₁ x₂ alpha) = TAFailedCast (weaken-ta-typ ub ta) x x₁ x₂ alpha
 