{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open import contexts

open import lemmas-consistency
open import lemmas-ground

open import lemmas-well-formed
open import rewrite-util
open import weakening
open import exchange

module lemmas-tysubst-ta where

  rewrite-codomain-in : ∀{t t' x Γ} -> t == t' -> (x , t) ∈ Γ -> (x , t') ∈ Γ
  rewrite-codomain-in eq p rewrite eq = p

  wf-unbound-tfresht : ∀{t τ Θ} -> t # Θ -> Θ ⊢ τ wf -> tunboundt-in t τ -> tfresht t τ
  wf-unbound-tfresht {τ = b} apt wf ub = TFBase
  wf-unbound-tfresht {t} {τ = T x} apt (WFVar int) UBTVar with natEQ t x 
  ... | Inl refl = TFTVar (abort (somenotnone ((! int) · apt)))
  ... | Inr neq = TFTVar neq
  wf-unbound-tfresht {τ = ⦇-⦈} apt wf ub = TFHole
  wf-unbound-tfresht {τ = τ ==> τ₁} apt (WFArr wf1 wf2) (UBArr ub1 ub2) = TFArr (wf-unbound-tfresht apt wf1 ub1) (wf-unbound-tfresht apt wf2 ub2)
  wf-unbound-tfresht {τ = ·∀ x τ} {Θ = Θ} apt (WFForall wf) (UBForall ne ub) = TFForall ne (wf-unbound-tfresht (lem-apart-extend {Γ = Θ} apt ne) wf ub)

  equiv-cond : ∀{Θ Θ'} -> ((τ : htyp) → Θ' ⊢ τ wf → Θ ⊢ τ wf) -> ((t : Nat) -> (t , <>) ∈ Θ' -> (t , <>) ∈ Θ)
  equiv-cond f = {!!}

  binders-tenvtfresh : ∀{Δ Γ Γ' t θ σ Θ Θ'} → Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ' → t # Θ → tunbound-in-θ t θ → tbinders-unique-θ θ → tenvtfresh t θ
  binders-tenvtfresh {t = t} {Θ' = Θ'} (STAIdId gsub tsub) apt ub bu with ctxindirect Θ' t 
  ... | Inl (<> , inl) = abort (somenotnone (! (equiv-cond  tsub t inl) · apt) )
  ... | Inr inr = TETFId inr
  binders-tenvtfresh (STAIdSubst ts x) apt ub bu = binders-tenvtfresh ts apt ub bu
  binders-tenvtfresh {Θ = Θ} (STASubst ts x) apt (UBθSubst x₁ ub x₂) (BUθSubst x₃ bu x₄) = TETFSubst (wf-unbound-tfresht apt x x₁) (binders-tenvtfresh ts (lem-apart-extend {Γ = Θ} apt x₂) ub bu) x₂

  lemma-typsubst-typsubst-comm : ∀{t1 t2 τ1 τ2 Δ Θ Θ' Γ Γ' θ σ} → Θ ⊢ τ2 wf → Δ , Θ , Γ ⊢ TypSubst τ1 t1 (TypSubst τ2 t2 θ) , σ :s: Θ' , Γ'
    → Δ , Θ , Γ ⊢ TypSubst τ2 t2 (TypSubst τ1 t1 θ) , σ :s: Θ' , Γ'
  lemma-typsubst-typsubst-comm {Θ = Θ} wf (STASubst (STASubst ts x₁) x) = STASubst (STASubst (rewrite-theta-subst (exchange-Θ {Θ = Θ}) ts) (weaken-t-wf x)) wf

  lemma-typsubst-subst-comm : ∀{Δ Θ Θ' Γ Γ' t τ τ' d y θ σ} →
    Δ , Θ , (Γ ,, (y , τ))  ⊢ TypSubst τ' t θ , σ :s: Θ' , Γ' →
    Δ , Θ , Γ ⊢ d :: τ →
    Δ , Θ , Γ ⊢ TypSubst τ' t θ , Subst d y σ :s: Θ' , Γ'
  lemma-typsubst-subst-comm {θ = TypId Θ} (STASubst (STAIdId gammasub thetasub) x) ta = STASubst (STAIdSubst (STAIdId gammasub thetasub) (weaken-ta-typ ta)) x
  lemma-typsubst-subst-comm {θ = TypId Θ} (STASubst (STAIdSubst ts ta) x) ta' = STASubst (STAIdSubst (STAIdSubst ts ta) (weaken-ta-typ ta')) x
  lemma-typsubst-subst-comm {θ = TypSubst τ t θ} (STASubst {τ = τ'} (STASubst ts x₁) x) ta = 
    STASubst (lemma-typsubst-subst-comm (STASubst ts x₁) (weaken-ta-typ ta)) x

  lemma-subst-comm : ∀{Δ Θ Θ' Γ Γ' τ d y θ σ} →
    Δ , Θ , (Γ ,, (y , τ))  ⊢ θ , σ :s: Θ' , Γ' →
    Δ , Θ , Γ ⊢ d :: τ →
    Δ , Θ , Γ ⊢ θ , Subst d y σ :s: Θ' , Γ'
  lemma-subst-comm {Δ} {Θ} {.Θ₁} {Γ} {Γ'} {τ} {d} {y} {TypId Θ₁} {.(Id Γ')} (STAIdId x x₁) ta = STAIdSubst (STAIdId x x₁) ta
  lemma-subst-comm {Δ} {Θ} {.Θ₁} {Γ} {Γ'} {τ} {d} {y} {TypId Θ₁} {.(Subst _ _ _)} (STAIdSubst ts x) ta = STAIdSubst (STAIdSubst ts x) ta
  lemma-subst-comm {Δ} {Θ} {Θ'} {Γ} {Γ'} {τ} {d} {y} {TypSubst τ₁ t θ} {σ} ts ta = lemma-typsubst-subst-comm ts ta

  gamma-sub-pres : ∀{Γ Γ' f} → ((x : Nat) (τ : htyp) → (x , τ) ∈ Γ' → (x , τ) ∈ Γ) → 
    ((x : Nat) (τ : htyp) → (x , τ) ∈ map f Γ' → (x , τ) ∈ map f Γ)
  gamma-sub-pres {Γ} {Γ'} {f} cond x τ mem with ctxindirect Γ x | ctxindirect Γ' x
  ... | _ | Inr ninr rewrite ninr = abort (somenotnone (! mem))
  ... | Inr ninl | Inl (tt , inr) rewrite ninl rewrite inr = abort (somenotnone ((! (cond x tt inr)) · ninl))
  ... | Inl (tt , inl) | Inl (tt' , inr) rewrite inl rewrite inr rewrite someinj (! inl · cond x tt' inr) = mem

  lemma-map-elem-sub : {A B : Set} -> (Γ Γ' : A ctx) -> {f : A -> B} -> ((x : Nat) (y : A) -> (x , y) ∈ Γ' -> (x , y) ∈ Γ) -> ((x : Nat) (y' : B) -> (x , y') ∈ map f Γ' -> (x , y') ∈ map f Γ)
  lemma-map-elem-sub Γ Γ' sub x y' inmg' with ctxindirect Γ' x
  ... | Inl (y , ing') rewrite ing' rewrite sub x y ing' = inmg'
  ... | Inr ning' rewrite ning' = abort (somenotnone (! inmg'))

  mutual
    lemma-strengthen-subst-typ : ∀{Δ Θ Θ' Γ Γ' θ σ t} -> tenvtfresh t θ -> Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' -> Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ'
    lemma-strengthen-subst-typ ef ts = {!!}

    lemma-tysubst-subst : ∀{Δ Θ Θ' Γ Γ' θ σ t τ} -> Θ ⊢ τ wf -> 
      Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' -> 
      Δ , Θ , Tctx[ τ / t ] Γ ⊢ TypSubst τ t θ , Sub[ τ / t ] σ :s: Θ' , (Tctx[ τ / t ] Γ')
    lemma-tysubst-subst {Γ = Γ} {Γ' = Γ'} wf (STAIdId x tsub) = STASubst (STAIdId (lemma-map-elem-sub Γ Γ' x) {! λ τ' x' → weaken-t-wf (tsub τ' x') !}) wf
    lemma-tysubst-subst {Γ = Γ} wf (STAIdSubst ts x) = lemma-typsubst-subst-comm (rewrite-gamma-subst (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst-subst wf ts)) (lemma-tysubst {!   !} {!   !} {!   !} {!   !}) -- (lemma-tysubst {!!} {!!} {!   !} {!   !} x)
    lemma-tysubst-subst {Θ = Θ} wf (STASubst ts x) = lemma-typsubst-typsubst-comm wf (STASubst (lemma-tysubst-subst (weaken-t-wf wf) {! ts !}) {! x !})

    lemma-tysubst : ∀{ Δ Γ Θ d t τ1 τ2 } -> 
      Δ hctxwf → Θ ⊢ τ2 wf -> t # Θ -> -- tbinders-unique d -> -- tunbound-in-Γ t Γ -> (Θ ,, (t , <>)) ⊢ Γ tctxwf -> 
      Δ , (Θ ,, (t , <>)), Γ ⊢ d :: τ1 -> 
      Δ , Θ , Tctx[ τ2 / t ] Γ ⊢ (Ihexp[ τ2 / t ] d) :: Typ[ τ2 / t ] τ1
    lemma-tysubst _ _ _ TAConst = TAConst
    lemma-tysubst {Γ = Γ} {t = t} {τ1 = τ1} {τ2 = τ2} _ wf apt (TAVar {x = x} ing) = TAVar (lem-map-preserve-elem {Γ = Γ} ing)
    lemma-tysubst {Γ = Γ} hcwf wf apt (TALam x x₁ ta) = 
      TALam (lem-map-preserve-apart {Γ = Γ} x) 
      ((wf-sub wf x₁ refl))
      (rewrite-gamma (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst hcwf wf apt ta))
    lemma-tysubst {t = t} hcwf wf apt (TATLam {t = t'} ta) with natEQ t t'
    ... | Inl refl = TATLam ({!   !})
    ... | Inr neq = TATLam {!   !}
    lemma-tysubst hcwf wf apt (TAAp ta ta') = TAAp (lemma-tysubst hcwf wf apt ta) (lemma-tysubst hcwf wf apt ta')
    lemma-tysubst {t = t} {τ2 = τ2} hcwf wf apt (TATAp {t = t'} {τ2 = τ4} {τ3 = τ3} x ta eq) with natEQ t t'
    ... | Inl refl rewrite natEQrefl {t'} rewrite natEQrefl {t} = TATAp {t = t'} {τ2 = τ4} ((wf-sub wf x refl))
                     (rewrite-typ (forall-sub-eq refl) (lemma-tysubst hcwf wf apt ta))
                     {!!} -- This one should be true if I have tfresht t tau2, which should be true if t # Theta or just by direct assumption
    ... | Inr neq rewrite natEQneq neq = TATAp {t = t'} {τ2 = Typ[ τ2 / t ] τ4} ((wf-sub wf x refl))
                    (rewrite-typ (forall-sub-neq neq) (lemma-tysubst hcwf wf apt ta)) {!!}
    lemma-tysubst {Δ = Δ} (HCtx hcwf) wf apt (TAEHole x ts eq eq') rewrite eq rewrite eq' = 
      let (Γ'wf , τ'wf) = hcwf x in TAEHole x (lemma-tysubst-subst wf ts) refl refl
    lemma-tysubst {Δ = Δ} hcwf wf apt (TANEHole x ta ts eq eq') rewrite eq rewrite eq' = TANEHole x (lemma-tysubst hcwf wf apt ta) (lemma-tysubst-subst wf ts) refl refl -- TANEHole x {!   !} {!   !} {!   !}
    lemma-tysubst hcwf wf apt (TACast ta x x~) = TACast (lemma-tysubst hcwf wf apt ta) ((wf-sub wf x refl)) {! (~Typ[] x~) !}
    lemma-tysubst hcwf wf apt (TAFailedCast ta tgnd tgnd' x) = TAFailedCast (lemma-tysubst hcwf wf apt ta) (ground-subst tgnd) (ground-subst tgnd') 
      λ eq → x {! (foo tgnd tgnd' eq) !}
      where
        foo : ∀{t1 t2 t3 t} -> t1 ground -> t2 ground -> Typ[ t3 / t ] t1 == Typ[ t3 / t ] t2 -> t1 == t2
        foo {t1} {t2} {t3} {t} g1 g2 eq rewrite ground-subst-id {t} {t1} {t3} g1 rewrite ground-subst-id {t} {t2} {t3} g2 = eq
      