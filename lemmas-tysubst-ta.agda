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
    {-
  lemma-tysubst : ∀{ Δ Γ Θ d τ t n } -> (n == typctx.n Θ) -> Θ ⊢ t wf -> [ Θ newtyp] ⊢ Γ tctxwf -> Δ , [ Θ newtyp] , Γ ⊢ d :: τ -> Δ , Θ , Tctx[ t / n ] Γ ⊢ (TTyp[ t / n ] d) :: Typ[ t / n ] τ
  lemma-tysubst _ _ _ TAConst = TAConst
  lemma-tysubst {Γ = Γ} {d = X var} {t = t} {n = n} nbound twf tcwf (TAVar x) = TAVar (lemma-subst-elem {Γ} {var} x)
  -}

  rewrite-codomain-in : ∀{t t' x Γ} -> t == t' -> (x , t) ∈ Γ -> (x , t') ∈ Γ
  rewrite-codomain-in eq p rewrite eq = p
  
  {-
    tbinders-fresh : ∀{ Δ Γ d2 τ y Θ} → Δ , Θ , Γ ⊢ d2 :: τ
                                      → binders-unique d2
                                      → unbound-in y d2
                                      → y # Γ
                                      → fresh y d2
-}

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

    lemma-tysubst-subst : ∀{ Δ Γ Γ' Θ Θ' t τ θ σ} -> 
      Θ ⊢ τ wf -> tunbound-in-Γ t Γ -> tunbound-in-θ t θ -> Θ ⊢ Γ tctxwf -> 
      Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' ->
      (Hctx[ τ / t ] Δ) , Θ , Tctx[ τ / t ] Γ ⊢ TypSubst τ t θ , (Sub[ τ / t ] σ) :s: Θ' , (Tctx[ τ / t ] Γ')
    lemma-tysubst-subst twf ubig ubtt tcwf (STAIdId gammasub thetasub) = STASubst (STAIdId (gamma-sub-pres gammasub) thetasub) twf
    lemma-tysubst-subst {Γ = Γ} twf ubig ubtt tcwf (STAIdSubst ts ta) = lemma-typsubst-subst-comm
        (rewrite-gamma-subst (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst-subst twf {!   !} ubtt (merge-tctx-wf tcwf (wf-ta tcwf {!   !} {! ta !})) ts)) 
        (lemma-tysubst twf ubig {! tcwf !} {!   !} {!   !} ta)
    lemma-tysubst-subst twf ubig ubtt tcwf (STASubst x x₁) = {!   !}
    {-
    lemma-tysubst-subst {Γ = Γ} {t = t} {τ = τ} twf _ _ _ (STAIdId x wf) = STAIdId (λ x' τ' ing → foo x' τ' x ing) λ τ' wf' → wf-tfresht {!   !} (wf τ' wf')
      where
        foo : ∀{Γ Γ' t τ} -> (x : Nat) (τ' : htyp) -> ((x₁ : Nat) (τ₁ : htyp) → (x₁ , τ₁) ∈ Γ' → (x₁ , τ₁) ∈ Γ) -> (x , τ') ∈ (Tctx[ τ / t ] Γ') -> (x , τ') ∈ (Tctx[ τ / t ] Γ)
        foo {Γ} {Γ'} {t} {τ} x τ' cond insub with ctxindirect Γ x | ctxindirect Γ' x
        ... | _ | Inr ninr rewrite ninr = abort (somenotnone (! insub))
        ... | Inr ninl | Inl (tt , inr) rewrite ninl rewrite inr = abort (somenotnone ((! (cond x tt inr)) · ninl))
        ... | Inl (tt , inl) | Inl (tt' , inr) rewrite inl rewrite inr rewrite someinj (! inl · cond x tt' inr) = insub
    lemma-tysubst-subst {t = t} {τ = τ} twf (UBTΓ ubtg) (UBθSubst ub ubtt ne) tcwf (STASubst {τ = τ'} sta x) = STASubst {!   !} (wf-tfresht {!   !} x)
    lemma-tysubst-subst twf (UBTΓ ubtg) ubtt tcwf (STAIdSubst subst ta) =
      STAIdSubst (rewrite-gamma-subst lem-map-extend-dist (lemma-tysubst-subst twf (UBTΓ {!   !}) ubtt (merge-tctx-wf tcwf (wf-ta tcwf {!   !} ta)) subst))
     (lemma-tysubst twf (UBTΓ ubtg) tcwf {!   !} {!   !}  ta)
    -}

    {- STASubst {τ = Typ[ τ / t ] τ'} 
      (rewrite-gamma-subst lem-map-extend-dist (lemma-tysubst-subst twf {! STASubst {τ = Typ[ τ / t ] τ'} 
      (rewrite-gamma-subst lem-map-extend-dist (lemma-tysubst-subst twf {!!} {!!} sta))
      (lemma-tysubst twf (UBTΓ ubtg) tcwf x)
    -}

    lemma-tysubst : ∀{ Δ Γ Θ d t τ1 τ2 } -> 
      Θ ⊢ τ2 wf -> tunbound-in-Γ t Γ -> Θ ⊢ Γ tctxwf -> 
      tbinderst-disjoint τ2 d -> tbinderst-unique τ2 ->
      Δ , (Θ ,, (t , <>)), Γ ⊢ d :: τ1 -> 
      (Hctx[ τ2 / t ] Δ) , Θ , (Tctx[ τ2 / t ] Γ) ⊢ (Ihexp[ τ2 / t ] d) :: Typ[ τ2 / t ] τ1
    lemma-tysubst _ _ _ _ _ TAConst = TAConst
    lemma-tysubst {Γ = Γ} {t = t} {τ1 = τ1} {τ2 = τ2} wf (UBTΓ ubtg) ctxwf tbd tbu (TAVar {x = x} ing) = TAVar (lem-map-preserve-elem {Γ = Γ} {f = (Typ[_/_]_) τ2 t}  ing) --(rewrite-codomain-in {Γ = Γ} (! (unbound-no-subst (ubtg x τ1 ing))) ing)
    lemma-tysubst {Γ = Γ} wf _ ctxwf tbd tbu (TALam x x₁ ta) = TALam (lem-map-preserve-apart {Γ = Γ} x) (wf-sub wf x₁ refl) (rewrite-gamma (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst wf {!  !} {!   !} {!   !} {!   !} ta)) -- (lemma-tysubst wf {!   !} {!   !} {!   !}) -- x (wf-sub wf x₁ refl) {!!}
    lemma-tysubst {t = t} wf ubtg ctxwf tbd tbu (TATLam {t = t'} ta) with natEQ t t'
    ... | Inl refl = TATLam ({!   !})
    ... | Inr neq = TATLam {!   !}
    lemma-tysubst wf ubig ctxwf tbd tbu (TAAp ta ta') = TAAp (lemma-tysubst wf ubig ctxwf {!   !} {!   !} ta) (lemma-tysubst wf ubig ctxwf {!   !} {!   !} ta')
    lemma-tysubst {t = t} {τ2 = τ2} wf ubtg ctxwf tbd tbu (TATAp {t = t'} {τ2 = τ4} {τ3 = τ3} x ta eq) with natEQ t t'
    ... | Inl refl rewrite natEQrefl {t'} rewrite natEQrefl {t} = TATAp {t = t'} {τ2 = τ4} (wf-sub wf x refl) 
                     (rewrite-typ (forall-sub-eq refl) (lemma-tysubst wf ubtg ctxwf {!   !} tbu ta))
                     {!!} -- This one should be true if I have tfresht t tau2, which should be true if t # Theta or just by direct assumption
    ... | Inr neq rewrite natEQneq neq = TATAp {t = t'} {τ2 = Typ[ τ2 / t ] τ4} (wf-sub wf x refl)
                    (rewrite-typ (forall-sub-neq neq) (lemma-tysubst wf ubtg ctxwf {!   !} tbu ta)) {!!}
    lemma-tysubst {Δ = Δ} {t = t} {τ1 = τ1} {τ2 = tau} wf _ ctxwf _ _ (TAEHole {σ = Id Γ} x x' eq) = TAEHole ((lem-map-preserve-elem {Γ = Δ} x)) {!!} {!!}
    lemma-tysubst {Δ = Δ} {Θ = Θ} wf ubig ctxwf tbd tbu (TAEHole {σ = Subst d y σ} x ts eq) rewrite eq = 
      TAEHole ((lem-map-preserve-elem {Γ = Δ} x))
        (lemma-tysubst-subst {!   !} {!   !} {!   !} {!   !} ts) refl -- wf ubig {!!} ctxwf {!!}) refl -- (STASubst (rewrite-theta-subst (! (typctx-contraction {Θ = Θ})) ts) (weaken-t-wf wf))) refl
    lemma-tysubst {Δ = Δ} {Θ = Θ} wf ubig ctxwf tbd tbu (TANEHole x ta ts eq) rewrite eq =
      TANEHole (lem-map-preserve-elem {Γ = Δ} x) 
        (lemma-tysubst {!   !} {!   !} {!   !} {!   !} {!   !} ta)
        (lemma-tysubst-subst wf ubig {!!} {! ctxwf !} ts) refl -- (STASubst (rewrite-theta-subst (! (typctx-contraction {Θ = Θ})) ts) (weaken-t-wf wf))) refl
    lemma-tysubst wf ubig ctxwf tbd tbu (TACast ta x x~) = TACast (lemma-tysubst wf ubig ctxwf {!   !} {!   !} ta) (wf-sub wf x refl) {! (~Typ[] x~) !}
    lemma-tysubst wf ubig ctxwf tbd tbu (TAFailedCast ta tgnd tgnd' x) = TAFailedCast (lemma-tysubst wf ubig ctxwf {!   !} tbu ta) (ground-subst tgnd) (ground-subst tgnd') 
      λ eq → x {! (foo tgnd tgnd' eq) !}
      where
        foo : ∀{t1 t2 t3 t} -> t1 ground -> t2 ground -> Typ[ t3 / t ] t1 == Typ[ t3 / t ] t2 -> t1 == t2
        foo {t1} {t2} {t3} {t} g1 g2 eq rewrite ground-subst-id {t} {t1} {t3} g1 rewrite ground-subst-id {t} {t2} {t3} g2 = eq
  