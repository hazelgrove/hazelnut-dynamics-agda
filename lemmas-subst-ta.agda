{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
open import Nat
open import core
open import contexts
open import weakening
open import exchange
open import lemmas-disjointness
open import binders-disjoint-checks
open import lemmas-alpha
open import lemmas-typ-subst

module lemmas-subst-ta where
  -- this is what makes the binders-unique assumption below good enough: it
  -- tells us that we can pick fresh variables
  mutual
    binders-envfresh : ∀{Δ Γ Γ' y θ σ Θ Θ'} → Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ' → y # Γ → unbound-in-σ y σ → binders-unique-σ σ → envfresh y σ
    binders-envfresh {Γ' = Γ'} {y = y} (STAIdId x _) apt unbound unique with ctxindirect Γ' y
    binders-envfresh {Γ' = Γ'} {y = y} (STAIdId x₁ _) apt unbound unique | Inl x = abort (somenotnone (! (x₁ y (π1 x) (π2 x)) · apt))
    binders-envfresh (STAIdId x₁ _) apt unbound unique | Inr x = EFId x
    binders-envfresh {Γ = Γ} {y = y} (STAIdSubst  {y = z} subst x₁ alpha) apt (UBσSubst x₂ unbound neq) (BUσSubst zz x₃ x₄) =
                                                                                    EFSubst (binders-fresh {y = y} x₁ zz x₂ apt)
                                                                                            (binders-envfresh subst (apart-extend1 Γ neq apt) unbound x₃)
                                                                                            neq
    binders-envfresh {Γ = Γ} {y = y} (STASubst subst wf) apt ub bu = binders-envfresh subst apt ub bu

    binders-fresh : ∀{ Δ Γ d2 τ y Θ} → Δ , Θ , Γ ⊢ d2 :: τ
                                      → binders-unique d2
                                      → unbound-in y d2
                                      → y # Γ
                                      → fresh y d2
    binders-fresh TAConst BUHole UBConst apt = FConst
    binders-fresh {y = y} (TAVar {x = x} x₁)  BUVar UBVar apt with natEQ y x
    binders-fresh (TAVar x₂) BUVar UBVar apt | Inl refl = abort (somenotnone (! x₂ · apt))
    binders-fresh (TAVar x₂) BUVar UBVar apt | Inr x₁ = FVar x₁
    binders-fresh {y = y} (TALam {x = x} x₁ wf wt) bu2 ub apt  with natEQ y x
    binders-fresh (TALam x₂ wf wt) bu2 (UBLam2 x₁ ub) apt | Inl refl = abort (x₁ refl)
    binders-fresh {Γ = Γ} (TALam {x = x} x₂ wf wt) (BULam bu2 x₃) (UBLam2 x₄ ub) apt | Inr x₁ =  FLam x₁ (binders-fresh wt bu2 ub (apart-extend1 Γ x₄ apt))
    binders-fresh {Γ = Γ} (TATLam apt wt) (BUTLam bu) (UBTLam ub2) x₃ = FTLam (binders-fresh wt bu ub2 x₃)
    binders-fresh (TAAp wt wt₁ alpha)  (BUAp bu2 bu3 x) (UBAp ub ub₁) apt = FAp (binders-fresh wt bu2 ub apt) (binders-fresh wt₁ bu3 ub₁ apt)
    binders-fresh (TATAp wf wt eq) (BUTAp x) (UBTAp x₂) x₃ = FTAp (binders-fresh wt x x₂ x₃)
    binders-fresh (TAEHole x₁ x₂ eq eq') (BUEHole x) (UBHole x₃) apt = FHole (binders-envfresh x₂ apt x₃ x )
    binders-fresh (TANEHole x₁ wt x₂ eq eq') (BUNEHole bu2 x) (UBNEHole x₃ ub) apt = FNEHole (binders-envfresh x₂ apt x₃ x) (binders-fresh wt bu2  ub apt)
    binders-fresh (TACast wt wf x₁ alpha) (BUCast bu2) (UBCast ub) apt = FCast (binders-fresh wt bu2 ub apt)
    binders-fresh (TAFailedCast wt x x₁ x₂ alpha) (BUFailedCast bu2) (UBFailedCast ub) apt = FFailedCast (binders-fresh wt bu2 ub apt)

  -- the substition lemma for preservation
  open alpha

  lem-subst : ∀{Δ Γ x τ1 τ1' d1 τ d2 Θ} →
                  x # Γ →
                  binders-disjoint d1 d2 →
                  binders-unique d2 →
                  tbinders-disjoint d1 d2 →
                  tbinders-unique d1 →
                  Δ , Θ , Γ ,, (x , τ1) ⊢ d1 :: τ →
                  Δ , Θ , Γ ⊢ d2 :: τ1' →
                  τ1 =α τ1' →
                  Σ[ τ' ∈ htyp ] (τ' =α τ × Δ , Θ , Γ ⊢ [ d2 / x ] d1 :: τ')
  lem-subst apt bd bu2 tbd tbu TAConst wt2 alpha = alpha-refl-ta TAConst
  lem-subst {x = x} apt bd bu2 tbd tbu (TAVar {x = x'} x₂) wt2 alpha with natEQ x' x
  lem-subst {Γ = Γ} apt bd bu2 tbd tbu (TAVar x₃) wt2 alpha | Inl refl with lem-apart-union-eq {Γ = Γ} apt x₃
  lem-subst {τ1' = τ1'} apt bd bu2 tbd tbu (TAVar x₃) wt2 alpha | Inl refl | refl = τ1' , alpha-sym alpha , wt2
  lem-subst {Γ = Γ} apt bd bu2 tbd tbu (TAVar x₃) wt2 alpha | Inr x₂ = alpha-refl-ta (TAVar (lem-neq-union-eq {Γ = Γ} x₂ x₃))
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d2 = d2} x#Γ (BDLam bd bd') bu2 (TBDLam tbd) (TBULam tbu) (TALam {x = y} {τ1 = τ1} {d = d} {τ2 = τ2} x₂ wf wt1) wt2 alpha
    with lem-union-none {Γ = Γ} x₂
  ... |  x≠y , y#Γ with natEQ y x
  ... | Inl eq = abort (x≠y (! eq)) 
  ... | Inr _ with lem-subst {Δ = Δ} {Γ = Γ ,, (y , τ1)} {x = x} {d1 = d} (apart-extend1 Γ x≠y x#Γ) bd bu2 tbd tbu (exchange-ta-Γ {Γ = Γ} x≠y wt1)
                                         (weaken-ta (binders-fresh wt2 bu2 bd' y#Γ) wt2) alpha
  ...   | τ' , alpha' , ta = τ1 ==> τ' , AlphaArr (alpha-refl τ1) alpha' , TALam y#Γ wf ta
  lem-subst {Γ = Γ} {Θ = Θ} apt (BDTLam bd) bu (TBDTLam tbd x) (TBUTLam tbu x₁) (TATLam {t = t} apt' wt1) wt2 alpha with lem-subst apt bd bu tbd tbu wt1 (weaken-ta-typ x wt2) alpha
  ... | τ' , alpha' , ta = let tub1 = tunbound-ta-tunboundt x {!   !} {!   !} wt2 in let tub2 = tunbound-ta-tunboundt x₁ {!   !} {!   !} wt1 in 
          ·∀ t τ' , {!   !} , TATLam apt' ta
  lem-subst apt (BDAp bd bd₁) bu3 (TBDAp tbd tbd') (TBUAp tbu tbu₁ x) (TAAp wt1 wt2 alpha') wt3 alpha with lem-subst apt bd bu3 tbd tbu wt1 wt3 alpha | lem-subst apt bd₁ bu3 tbd' tbu₁ wt2 wt3 alpha
  ... | τ'1 ==> τ'2 , AlphaArr alpha'1 alpha'2 , ta | τ'' , alpha'' , ta' = τ'2 , alpha'2 , TAAp ta ta' (alpha-trans alpha'1 (alpha-trans alpha' (alpha-sym alpha'')))
  lem-subst apt (BDTAp bd) bu (TBDTAp tbtd tbd) (TBUTAp tbu x x₁) (TATAp {τ1 = τ} wf wt1 eq) wt2 alpha with lem-subst apt bd bu tbd tbu wt1 wt2 alpha
  ... | ·∀ t' τ' , alpha' , ta rewrite ! eq = Typ[ τ / t' ] τ' , {!   !} , TATAp wf ta refl
  lem-subst apt bd bu2 (TBDHole x x') (TBUEHole x₁ x₂ x₃) (TAEHole inΔ sub eq eq') wt2 alpha = alpha-refl-ta (TAEHole inΔ (lemma-subst-comm (lemma-tbdθσ-comm x₃ x) sub {!   !}) eq eq')
  lem-subst apt (BDNEHole x₁ bd) bu2 (TBDNEHole x x' tbd) (TBUNEHole tbu x₂ x₅ x₆) (TANEHole x₃ wt1 x₄ eq eq') wt2 alpha with lem-subst apt bd bu2 tbd tbu wt1 wt2 alpha
  ... | τ' , alpha' , ta = alpha-refl-ta (TANEHole x₃ ta (lemma-subst-comm (lemma-tbdθσ-comm x₆ x) x₄ {!   !}) eq eq')
  lem-subst apt (BDCast bd) bu2 (TBDCast tbd) (TBUCast tbu x x₂) (TACast wt1 wf x₁ alpha') wt2 alpha with lem-subst apt bd bu2 tbd tbu wt1 wt2 alpha
  ... | τ' , alpha'' , ta = alpha-refl-ta (TACast ta wf x₁ (alpha-trans alpha' (alpha-sym alpha'')))
  lem-subst apt (BDFailedCast bd) bu2 (TBDFailedCast tbd) (TBUFailedCast tbu x x₄) (TAFailedCast wt1 x₁ x₂ x₃ alpha') wt2 alpha with lem-subst apt bd bu2 tbd tbu wt1 wt2 alpha
  ... | τ' , alpha'' , ta = alpha-refl-ta (TAFailedCast ta x₁ x₂ x₃ (alpha-trans alpha' (alpha-sym alpha'')))
  