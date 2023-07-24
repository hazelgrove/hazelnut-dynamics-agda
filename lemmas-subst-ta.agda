open import Prelude
open import Nat
open import core
open import contexts
open import weakening
open import exchange
open import lemmas-disjointness
open import binders-disjoint-checks
-- open import lemmas-free-tvars

module lemmas-subst-ta where
  -- this is what makes the binders-unique assumption below good enough: it
  -- tells us that we can pick fresh variables
  mutual
    binders-envfresh : ∀{Δ Γ Γ' y σ Θ} → Δ , Θ , Γ ⊢ σ :s: Γ' → y # Γ → unbound-in-σ y σ → binders-unique-σ σ → envfresh y σ
    binders-envfresh {Γ' = Γ'} {y = y} (STAId x) apt unbound unique with ctxindirect Γ' y
    binders-envfresh {Γ' = Γ'} {y = y} (STAId x₁) apt unbound unique | Inl x = abort (somenotnone (! (x₁ y (π1 x) (π2 x)) · apt))
    binders-envfresh (STAId x₁) apt unbound unique | Inr x = EFId x
    binders-envfresh {Γ = Γ} {y = y} (STASubst  {y = z} subst x₁) apt (UBσSubst x₂ unbound neq) (BUσSubst zz x₃ x₄) =
                                                                                    EFSubst (binders-fresh {y = y} x₁ zz x₂ apt)
                                                                                            (binders-envfresh subst (apart-extend1 Γ neq apt) unbound x₃)
                                                                                            neq
    
    {-
    binders-envtfresh : ∀{Δ Γ Γ' y σ Θ} → Δ , Θ , Γ ⊢ σ :s: Γ' → y # Θ → unbound-in-σ y σ → binders-unique-σ σ → unboundt-in-Γ y Γ -> envtfresh y σ
    binders-envtfresh {Γ' = Γ'} {y = y} {Θ = Θ} (STAId x) apt ub bu (UBTΓ ubtg) = ETFId (UBTΓ \k v inc ->  ubtg k v (x k v inc))
    binders-envtfresh (STASubst ta x) apt (UBσSubst x₁ ub x₂) (BUσSubst x₃ bu x₄) (UBTΓ ubtg) = 
      let y-tfresh = (binders-tfresh x x₃ x₁ apt) in
      ETFSubst y-tfresh
               (binders-envtfresh ta apt ub bu {!   !}) x₂ -}

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
    binders-fresh {Γ = Γ} (TATLam wt) (BUTLam bu ub1) (UBTLam ne ub2) x₃ = FTLam (binders-fresh wt bu ub2 x₃)
    binders-fresh (TAAp wt wt₁)  (BUAp bu2 bu3 x) (UBAp ub ub₁) apt = FAp (binders-fresh wt bu2 ub apt) (binders-fresh wt₁ bu3 ub₁ apt)
    binders-fresh (TATAp wf wt eq) (BUTAp x) (UBTAp x₂) x₃ = FTAp (binders-fresh wt x x₂ x₃)
    binders-fresh (TAEHole x₁ x₂) (BUEHole x) (UBHole x₃) apt = FHole (binders-envfresh x₂ apt x₃ x )
    binders-fresh (TANEHole x₁ wt x₂) (BUNEHole bu2 x) (UBNEHole x₃ ub) apt = FNEHole (binders-envfresh x₂ apt x₃ x) (binders-fresh wt bu2  ub apt)
    binders-fresh (TACast wt wf x₁) (BUCast bu2) (UBCast ub) apt = FCast (binders-fresh wt  bu2  ub apt)
    binders-fresh (TAFailedCast wt x x₁ x₂) (BUFailedCast bu2) (UBFailedCast ub) apt = FFailedCast (binders-fresh wt  bu2  ub apt)
{-
    binders-tfresh : ∀{ Δ Γ d2 τ y Θ} → Δ , Θ , Γ ⊢ d2 :: τ
                                      → binders-unique d2
                                      → unbound-in y d2
                                      → y # Θ
                                      → tfresh y d2
    binders-tfresh TAConst BUHole UBConst apt = TFConst
    binders-tfresh (TAVar x) BUVar UBVar apt = TFVar
    binders-tfresh (TALam x₁ x₂ ta) (BULam bu x) (UBLam2 x₃ ub) apt = TFLam {!   !} (binders-tfresh ta bu ub apt)
    binders-tfresh {Θ = Θ} (TATLam apt ta) (BUTLam bu x) (UBTLam ne ub) apt' = TFTLam ne (binders-tfresh ta bu ub (apart-extend1 Θ ne apt'))
    binders-tfresh (TAEHole x₂ x₃) (BUEHole x) (UBHole x₁) apt = TFHole (binders-envtfresh x₃ apt x₁ x {!!})
    binders-tfresh ta (BUNEHole bu x) ub apt = {!   !}
    binders-tfresh ta (BUAp bu bu₁ x) ub apt = {!   !}
    binders-tfresh ta (BUTAp bu) ub apt = {!   !}
    binders-tfresh ta (BUCast bu) ub apt = {!   !}
    binders-tfresh ta (BUFailedCast bu) ub apt = {!   !}
-}
  -- the substition lemma for preservation
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 Θ} →
                  x # Γ →
                  binders-disjoint d1 d2 →
                  binders-unique d2 →
                  Δ , Θ , Γ ,, (x , τ1) ⊢ d1 :: τ →
                  Δ , Θ , Γ ⊢ d2 :: τ1 →
                  Δ , Θ , Γ ⊢ [ d2 / x ] d1 :: τ
  lem-subst apt bd bu2  TAConst wt2 = TAConst
  lem-subst {x = x} apt bd bu2  (TAVar {x = x'} x₂) wt2 with natEQ x' x
  lem-subst {Γ = Γ} apt bd bu2 (TAVar x₃) wt2 | Inl refl with lem-apart-union-eq {Γ = Γ} apt x₃
  lem-subst apt bd bu2  (TAVar x₃) wt2 | Inl refl | refl = wt2
  lem-subst {Γ = Γ} apt bd bu2  (TAVar x₃) wt2 | Inr x₂ = TAVar (lem-neq-union-eq {Γ = Γ} x₂ x₃)
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d2 = d2} x#Γ (BDLam bd bd') bu2 (TALam {x = y} {τ1 = τ1} {d = d} {τ2 = τ2} x₂ wf wt1) wt2
    with lem-union-none {Γ = Γ} x₂
  ... |  x≠y , y#Γ with natEQ y x
  ... | Inl eq = abort (x≠y (! eq))
  ... | Inr _  = TALam y#Γ wf (lem-subst {Δ = Δ} {Γ = Γ ,, (y , τ1)} {x = x} {d1 = d} (apart-extend1 Γ x≠y x#Γ) bd bu2 (exchange-ta-Γ {Γ = Γ} x≠y wt1)
                                         (weaken-ta (binders-fresh wt2 bu2 bd' y#Γ) wt2))
  lem-subst {Γ = Γ} {Θ = Θ} apt (BDTLam bd ub) bu (TATLam wt1) wt2 = TATLam (lem-subst apt bd bu wt1 (weaken-ta-typ wt2))
  lem-subst apt (BDAp bd bd₁) bu3 (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt bd bu3 wt1 wt3) (lem-subst apt bd₁ bu3 wt2 wt3)
  lem-subst apt (BDTAp bd) bu (TATAp wf wt1 eq) wt2 = TATAp wf (lem-subst apt bd bu wt1 wt2) eq
  lem-subst apt bd bu2 (TAEHole inΔ sub) wt2 = TAEHole inΔ (STASubst sub wt2)
  lem-subst apt (BDNEHole x₁ bd) bu2 (TANEHole x₃ wt1 x₄) wt2 = TANEHole x₃ (lem-subst apt bd bu2 wt1 wt2) (STASubst x₄ wt2)
  lem-subst apt (BDCast bd) bu2 (TACast wt1 wf x₁) wt2 = TACast (lem-subst apt bd bu2 wt1 wt2) wf x₁
  lem-subst apt (BDFailedCast bd) bu2 (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt bd bu2 wt1 wt2) x₁ x₂ x₃
 