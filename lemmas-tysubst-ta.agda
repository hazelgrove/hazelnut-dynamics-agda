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


  lemma-typsubst-typsubst-comm : ∀{t1 t2 τ1 τ2 Δ Θ Θ' Γ Γ' θ σ} → tunboundt-in t1 τ2 → tunboundt-in t2 τ1 → Δ , Θ , Γ ⊢ TypSubst τ1 t1 (TypSubst τ2 t2 θ) , σ :s: Θ' , Γ'
    → Δ , Θ , Γ ⊢ TypSubst τ2 t2 (TypSubst τ1 t1 θ) , σ :s: Θ' , Γ'
  lemma-typsubst-typsubst-comm ub1 ub2 ts = {! ts !}

  lemma-typsubst-subst-comm : ∀{Δ Θ Θ' Γ Γ' t τ τ' d y θ σ} →
    Δ , Θ , (Γ ,, (y , τ))  ⊢ TypSubst τ' t θ , σ :s: Θ' , Γ' →
    Δ , Θ , Γ ⊢ d :: τ →
    Δ , Θ , Γ ⊢ TypSubst τ' t θ , Subst d y σ :s: Θ' , Γ'
  lemma-typsubst-subst-comm {θ = TypId Θ} (STASubst (STAIdId gammasub thetasub) x) ta = STASubst (STAIdSubst (STAIdId gammasub thetasub) (weaken-ta-typ ta)) x
  lemma-typsubst-subst-comm {θ = TypId Θ} (STASubst (STAIdSubst ts ta) x) ta' = STASubst (STAIdSubst (STAIdSubst ts ta) (weaken-ta-typ ta')) x
  lemma-typsubst-subst-comm {θ = TypSubst τ t θ} (STASubst {τ = τ'} (STASubst ts x₁) x) ta = 
    STASubst (lemma-typsubst-subst-comm (STASubst ts x₁) (weaken-ta-typ ta)) x

  gamma-sub-pres : ∀{Γ Γ' f} → ((x : Nat) (τ : htyp) → (x , τ) ∈ Γ' → (x , τ) ∈ Γ) → 
    ((x : Nat) (τ : htyp) → (x , τ) ∈ map f Γ' → (x , τ) ∈ map f Γ)
  gamma-sub-pres {Γ} {Γ'} {f} cond x τ mem with ctxindirect Γ x | ctxindirect Γ' x
  ... | _ | Inr ninr rewrite ninr = abort (somenotnone (! mem))
  ... | Inr ninl | Inl (tt , inr) rewrite ninl rewrite inr = abort (somenotnone ((! (cond x tt inr)) · ninl))
  ... | Inl (tt , inl) | Inl (tt' , inr) rewrite inl rewrite inr rewrite someinj (! inl · cond x tt' inr) = mem

  mutual

    lemma-tysubst-subst : ∀{Δ Θ' Γ Γ' θ σ t τ} -> ∅ ⊢ τ wf -> Δ , (∅ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' -> Δ , ∅ , Tctx[ τ / t ] Γ ⊢ TypSubst τ t θ , σ :s: Θ' , Γ'
    lemma-tysubst-subst wf (STAIdId x x₁) = STASubst {!!} wf
    lemma-tysubst-subst wf (STAIdSubst ts x) = {!   !}
    lemma-tysubst-subst wf (STASubst ts x) = {!   !}

    lemma-tysubst : ∀{ Δ Γ d t τ1 τ2 } -> 
      ∅ ⊢ τ2 wf -> tunbound-in-Γ t Γ -> ∅ ⊢ Γ tctxwf -> 
      Δ , (∅ ,, (t , <>)), Γ ⊢ d :: τ1 -> 
      Δ , ∅ , Tctx[ τ2 / t ] Γ ⊢ (Ihexp[ τ2 / t ] d) :: Typ[ τ2 / t ] τ1
    lemma-tysubst _ _ _ TAConst = TAConst
    lemma-tysubst {Γ = Γ} {t = t} {τ1 = τ1} {τ2 = τ2} wf (UBTΓ ubtg) ctxwf (TAVar {x = x} ing) = {! TAVar (rewrite-codomain-in {Γ = Γ} (t-sub-closed ? ) ing) !}
    lemma-tysubst {Γ = Γ} wf _ ctxwf (TALam x x₁ ta) = TALam {! x !} (wf-sub wf x₁ refl) {!!} -- (lemma-tysubst wf {!  !} {!   !}  {!  !} ) -- (lemma-tysubst wf {!   !} {!   !} {!   !}) -- x (wf-sub wf x₁ refl) {!!}
    lemma-tysubst {t = t} wf ubtg ctxwf (TATLam {t = t'} ta) with natEQ t t'
    ... | Inl refl = TATLam ({!   !})
    ... | Inr neq = TATLam {!   !}
    lemma-tysubst wf ubig ctxwf (TAAp ta ta') = TAAp (lemma-tysubst wf ubig ctxwf  ta) (lemma-tysubst wf ubig ctxwf  ta')
    lemma-tysubst {t = t} {τ2 = τ2} wf ubtg ctxwf (TATAp {t = t'} {τ2 = τ4} {τ3 = τ3} x ta eq) with natEQ t t'
    ... | Inl refl rewrite natEQrefl {t'} rewrite natEQrefl {t} = TATAp {t = t'} {τ2 = τ4} (wf-sub wf x refl) 
                     (rewrite-typ (forall-sub-eq refl) (lemma-tysubst wf ubtg ctxwf  ta))
                     {!!} -- This one should be true if I have tfresht t tau2, which should be true if t # Theta or just by direct assumption
    ... | Inr neq rewrite natEQneq neq = TATAp {t = t'} {τ2 = Typ[ τ2 / t ] τ4} (wf-sub wf x refl)
                    (rewrite-typ (forall-sub-neq neq) (lemma-tysubst wf ubtg ctxwf  ta)) {!!}
    lemma-tysubst {Δ = Δ} {t = t} {τ1 = τ1} {τ2 = tau} wf _ ctxwf (TAEHole {σ = Id Γ} x x' eq) = TAEHole x {!!} {!!}
    lemma-tysubst {Δ = Δ} wf ubig ctxwf (TAEHole {σ = Subst d y σ} x ts eq) rewrite eq = 
      TAEHole x
        {!   !} {!   !} -- (lemma-tysubst-subst {!   !} {!   !} {!   !} {!   !} ts) refl -- wf ubig {!!} ctxwf {!!}) refl -- (STASubst (rewrite-theta-subst (! (typctx-contraction {Θ = Θ})) ts) (weaken-t-wf wf))) refl
    lemma-tysubst {Δ = Δ} wf ubig ctxwf (TANEHole x ta ts eq) rewrite eq = TANEHole x {!   !} {!   !} {!   !}
      -- TANEHole x
      --   {! ((lemma-tysubst ? ? ? ta)) !}
      --   {!   !} refl -- (lemma-tysubst-subst wf ubig {!!} {! ctxwf !} ts) refl -- (STASubst (rewrite-theta-subst (! (typctx-contraction {Θ = Θ})) ts) (weaken-t-wf wf))) refl
    lemma-tysubst wf ubig ctxwf (TACast ta x x~) = TACast (lemma-tysubst wf ubig ctxwf ta) (wf-sub wf x refl) {! (~Typ[] x~) !}
    lemma-tysubst wf ubig ctxwf (TAFailedCast ta tgnd tgnd' x) = TAFailedCast (lemma-tysubst wf ubig ctxwf  ta) (ground-subst tgnd) (ground-subst tgnd') 
      λ eq → x {! (foo tgnd tgnd' eq) !}
      where
        foo : ∀{t1 t2 t3 t} -> t1 ground -> t2 ground -> Typ[ t3 / t ] t1 == Typ[ t3 / t ] t2 -> t1 == t2
        foo {t1} {t2} {t3} {t} g1 g2 eq rewrite ground-subst-id {t} {t1} {t3} g1 rewrite ground-subst-id {t} {t2} {t3} g2 = eq
    