{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-disjointness
open import exchange
open import rewrite-util

-- this module contains all the proofs of different weakening structural
-- properties that we use for the hypothetical judgements
module weakening where
  weaken-t-wf : ∀ {Θ x τ} → Θ ⊢ τ wf → (Θ ,, (x , <>)) ⊢ τ wf
  weaken-t-wf {Θ} (WFVar x) = WFVar (x∈∪l Θ _ _ <> x)
  weaken-t-wf WFBase = WFBase
  weaken-t-wf WFHole = WFHole
  weaken-t-wf (WFArr wf wf₁) = WFArr (weaken-t-wf wf) (weaken-t-wf wf₁)
  weaken-t-wf {Θ} (WFForall wf) = WFForall (exchange-wf {Θ = Θ} (weaken-t-wf wf))
  
  {-with natEQ x y
  ... | Inl refl = WFForall (abort (ne refl)) 
  ... | Inr neq = WFForall (exchange-wf {y} {x} {t} {Θ} (flip neq) {! wf  !})
  -}

  weaken-tctx-wf : ∀ {Θ Γ x} → Θ ⊢ Γ tctxwf → (Θ ,, (x , <>)) ⊢ Γ tctxwf
  weaken-tctx-wf (CCtx x) = CCtx (λ x₁ → weaken-t-wf (x x₁))

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
    weaken-subst-Δ disj (STAIdSubst subst x) = STAIdSubst (weaken-subst-Δ disj subst) (weaken-ta-Δ1 disj x)
    weaken-subst-Δ disj (STASubst subst x) = STASubst (weaken-subst-Δ disj subst) x

    weaken-ta-Δ1 : ∀{Δ1 Δ2 Γ d τ Θ} → Δ1 ## Δ2
                                  → Δ1 , Θ , Γ ⊢ d :: τ
                                  → (Δ1 ∪ Δ2) , Θ , Γ ⊢ d :: τ
    weaken-ta-Δ1 disj TAConst = TAConst
    weaken-ta-Δ1 disj (TAVar x₁) = TAVar x₁
    weaken-ta-Δ1 disj (TALam x₁ wf wt) = TALam x₁ wf (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TATLam wt) = TATLam (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TAAp wt wt₁) = TAAp (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁)
    weaken-ta-Δ1 disj (TATAp wf wt eq) = TATAp wf (weaken-ta-Δ1 disj wt) eq
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TAEHole {u = u} {Γ' = Γ'} x x₁ eq) = TAEHole (x∈∪l Δ1 Δ2 u _ x ) (weaken-subst-Δ disj x₁) eq
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TANEHole {Γ' = Γ'} {u = u} x wt x₁ eq) = TANEHole (x∈∪l Δ1 Δ2 u _ x) (weaken-ta-Δ1 disj wt) (weaken-subst-Δ disj x₁) eq
    weaken-ta-Δ1 disj (TACast wt wf x) = TACast (weaken-ta-Δ1 disj wt) wf x
    weaken-ta-Δ1 disj (TAFailedCast wt x x₁ x₂) = TAFailedCast (weaken-ta-Δ1 disj wt) x x₁ x₂

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
    weaken-subst-Γ {Γ = Γ} (EFId x₁) (STAIdId x₂ prem) = STAIdId (λ x τ x₃ → x∈∪l Γ _ x τ (x₂ x τ x₃) ) {!!}
    weaken-subst-Γ {x = x} {Γ = Γ} (EFSubst x₁ efrsh x₂) (STAIdSubst {y = y} {τ = τ'} subst x₃) =
      STAIdSubst (exchange-subst-Γ {Γ = Γ} (flip x₂) (weaken-subst-Γ {Γ = Γ ,, (y , τ')} efrsh subst))
               (weaken-ta x₁ x₃)
    weaken-subst-Γ (EFId x) (STASubst x₁ x₂) = {!!}
    weaken-subst-Γ {x = x} {Γ = Γ} (EFSubst x₁ efrsh x₂) (STASubst {y = y} {τ = τ'} subst x₃) =
      STASubst {!   !} -- (exchange-subst-Γ {Γ = Γ} (flip x₂) (weaken-subst-Γ {Γ = Γ ,, (y , τ')} efrsh subst))
               {!   !} --(weaken-ta x₁ x₃)

    weaken-ta : ∀{x Γ Δ d τ τ' Θ} →
                fresh x d →
                Δ , Θ , Γ ⊢ d :: τ →
                Δ , Θ , Γ ,, (x , τ') ⊢ d :: τ
    weaken-ta _ TAConst = TAConst
    weaken-ta {x} {Γ} {_} {_} {τ} {τ'} (FVar x₂) (TAVar x₃) = TAVar (x∈∪l Γ (■ (x , τ')) _ _ x₃)
    weaken-ta {x = x} frsh (TALam {x = y} apt wf wt) with natEQ x y
    weaken-ta (FLam x₁ x₂) (TALam apt wf wt) | Inl refl = abort (x₁ refl)
    weaken-ta {Γ = Γ} {τ' = τ'} (FLam x₁ x₃) (TALam {x = y} x₄ wf wt) | Inr x₂ = TALam (apart-extend1 Γ (flip x₁) x₄) wf (exchange-ta-Γ {Γ = Γ} (flip x₁) (weaken-ta x₃ wt))
    weaken-ta {x} {Γ} {τ' = τ'} (FTLam frsh) (TATLam x₁) = TATLam (rewrite-gamma {!!} ((weaken-ta frsh x₁)))
    weaken-ta (FAp frsh frsh₁) (TAAp wt wt₁) = TAAp (weaken-ta frsh wt) (weaken-ta frsh₁ wt₁)
    weaken-ta (FTAp frsh) (TATAp wf x₁ eq) = TATAp wf (weaken-ta frsh x₁) eq
    weaken-ta (FHole x₁) (TAEHole x₂ x₃ eq) = TAEHole x₂ (weaken-subst-Γ x₁ x₃) eq
    weaken-ta (FNEHole x₁ frsh) (TANEHole x₂ wt x₃ eq) = TANEHole x₂ (weaken-ta frsh wt) (weaken-subst-Γ x₁ x₃) eq
    weaken-ta (FCast frsh) (TACast wt wf x₁) = TACast (weaken-ta frsh wt) wf x₁
    weaken-ta (FFailedCast frsh) (TAFailedCast wt x₁ x₂ x₃) = TAFailedCast (weaken-ta frsh wt) x₁ x₂ x₃

  mutual 
    weaken-subst-Θ : ∀{Γ Δ θ t σ Γ' Θ Θ'} →
                     Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ' →
                     Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ'
    weaken-subst-Θ (STAIdId x p) = STAIdId x {!!}
    weaken-subst-Θ (STAIdSubst x x₁) = {!!}
    weaken-subst-Θ (STASubst x x₁) = STASubst {! (weaken-subst-Θ x) !} {! (weaken-ta-typ x₁) !}
    
    weaken-ta-typ : ∀{Γ Δ Θ d t τ} →
                    Δ , Θ , Γ ⊢ d :: τ →
                    Δ , (Θ ,, (t , <>)) , Γ ⊢ d :: τ
    weaken-ta-typ TAConst = TAConst
    weaken-ta-typ (TAVar x) = TAVar x
    weaken-ta-typ (TALam x x₁ x₂) = TALam x (weaken-t-wf x₁) (weaken-ta-typ x₂)
    weaken-ta-typ (TATLam x) = TATLam {! (weaken-ta-typ x) !}
    weaken-ta-typ (TAAp x x₁) = TAAp (weaken-ta-typ x) (weaken-ta-typ x₁)
    weaken-ta-typ (TATAp wf x eq) = TATAp (weaken-t-wf wf) (weaken-ta-typ x) eq
    weaken-ta-typ (TAEHole x x₁ eq) = TAEHole x (weaken-subst-Θ x₁) eq
    weaken-ta-typ (TANEHole x x₁ x₂ eq) = TANEHole x (weaken-ta-typ x₁) (weaken-subst-Θ x₂) eq
    weaken-ta-typ (TACast x wf x₁) = TACast (weaken-ta-typ x) (weaken-t-wf wf) x₁
    weaken-ta-typ (TAFailedCast x x₁ x₂ x₃) = TAFailedCast (weaken-ta-typ x) x₁ x₂ x₃
