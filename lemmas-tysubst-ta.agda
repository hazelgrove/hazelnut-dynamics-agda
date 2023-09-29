{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open import contexts

open import lemmas-consistency
open import lemmas-ground
open import lemmas-alpha

open import lemmas-well-formed
open import lemmas-typ-subst
open import rewrite-util
open import weakening
open import exchange

module lemmas-tysubst-ta where

  rewrite-codomain-in : ∀{t : htyp} {t' x Γ} -> t == t' -> (x , t) ∈ Γ -> (x , t') ∈ Γ
  rewrite-codomain-in eq p rewrite eq = p

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

  lemma-typ-typ-1 : ∀{τ1 τ2 t} → (τ : htyp) → ∅ ⊢ τ2 wf → Typ[ Typ[ τ2 / t ] τ1 / t ] τ == Typ[ τ2 / t ] (Typ[ τ1 / t ] τ)
  lemma-typ-typ-1 b wf = refl
  lemma-typ-typ-1 {t = t} (T x) wf with natEQ t x
  ... | Inl refl = refl
  ... | Inr neq rewrite natEQneq neq = refl
  lemma-typ-typ-1 ⦇-⦈ wf = refl
  lemma-typ-typ-1 (τ ==> τ₁) wf = arr-eq (lemma-typ-typ-1 τ wf) (lemma-typ-typ-1 τ₁ wf)
  lemma-typ-typ-1 {t = t} (·∀ x τ) wf with natEQ t x 
  ... | Inl refl rewrite natEQrefl {x} = refl
  ... | Inr neq rewrite natEQneq neq = forall-eq refl (lemma-typ-typ-1 τ wf)

  lemma-typ-typ-2 : ∀{τ1 τ2 t t'} → (τ : htyp) → tunboundt-in t τ → ∅ ⊢ τ2 wf → t ≠ t' → Typ[ Typ[ τ2 / t ] τ1 / t' ] (Typ[ τ2 / t ] τ) == Typ[ τ2 / t ] (Typ[ τ1 / t' ] τ)
  lemma-typ-typ-2 b _ wf neq = refl
  lemma-typ-typ-2 {t = t} {t' = t'} (T x) _ wf neq with natEQ t x
  ... | Inl refl rewrite natEQneq (flip neq) rewrite natEQrefl {x} = t-sub-closed wf
  ... | Inr neq' with natEQ t' x
  ...   | Inl refl = refl
  ...   | Inr neq'' rewrite natEQneq neq' = refl
  lemma-typ-typ-2 ⦇-⦈ _ wf neq = refl
  lemma-typ-typ-2 (τ ==> τ₁) (UBArr ub ub₁) wf neq = arr-eq (lemma-typ-typ-2 τ ub wf neq) (lemma-typ-typ-2 τ₁ ub₁ wf neq)
  lemma-typ-typ-2 {τ1} {τ2} {t = t} {t' = t'} (·∀ x τ) ub wf neq with natEQ t x
  ... | Inl refl rewrite natEQneq (flip neq) rewrite natEQrefl {x} with ub 
  ...   | (UBForall nequb ub) = abort (nequb refl)
  lemma-typ-typ-2 {τ1} {τ2} {t = t} {t' = t'} (·∀ x τ) ub wf neq | Inr neq' with natEQ t' x
  ...   | Inl refl rewrite natEQneq neq = refl
  ...   | Inr neq'' rewrite natEQneq neq' with ub
  ...     | (UBForall nequb ub) = forall-eq refl (lemma-typ-typ-2 τ ub wf neq)

  unbound-typ-sub : ∀{t τ τ'} → tunboundt-in t τ → tunboundt-in t τ' → tunboundt-in t (Typ[ τ' / t ] τ)
  unbound-typ-sub UBBase ub' = UBBase
  unbound-typ-sub {t} (UBTVar {t' = t'}) ub' with natEQ t t'
  ... | Inl refl = ub'
  ... | Inr neq = UBTVar
  unbound-typ-sub UBHole ub' = UBHole
  unbound-typ-sub (UBArr ub ub₁) ub' = UBArr (unbound-typ-sub ub ub') (unbound-typ-sub ub₁ ub')
  unbound-typ-sub {t} (UBForall {t' = t'} x ub) ub' with natEQ t t'
  ... | Inl refl = UBForall (λ _ → x refl) ub
  ... | Inr neq = UBForall x (unbound-typ-sub ub ub')

  mutual
    unbound-ihexp-sub : ∀{t τ d} → tunbound-in t d → tunboundt-in t τ → tunbound-in t (Ihexp[ τ / t ] d)
    unbound-ihexp-sub TUBConst ubt = TUBConst
    unbound-ihexp-sub TUBVar ubt = TUBVar
    unbound-ihexp-sub (TUBLam2 ub x) ubt = TUBLam2 (unbound-ihexp-sub ub ubt) (unbound-typ-sub x ubt)
    unbound-ihexp-sub {t = t} (TUBTLam {t' = t'} x ub) ubt with natEQ t t'
    ... | Inl refl = TUBTLam (λ _ → x refl) ub
    ... | Inr neq = TUBTLam x (unbound-ihexp-sub ub ubt)
    unbound-ihexp-sub (TUBHole x x₁) ubt = TUBHole (UBθSubst ubt x) (unbound-sub-sub x₁ ubt)
    unbound-ihexp-sub (TUBNEHole x x₁ ub) ubt = TUBNEHole (UBθSubst ubt x) (unbound-sub-sub x₁ ubt) (unbound-ihexp-sub ub ubt)
    unbound-ihexp-sub (TUBAp ub ub₁) ubt = TUBAp (unbound-ihexp-sub ub ubt) (unbound-ihexp-sub ub₁ ubt)
    unbound-ihexp-sub (TUBTAp ub x) ubt = TUBTAp (unbound-ihexp-sub ub ubt) (unbound-typ-sub x ubt)
    unbound-ihexp-sub (TUBCast ub x x₁) ubt = TUBCast (unbound-ihexp-sub ub ubt) (unbound-typ-sub x ubt) (unbound-typ-sub x₁ ubt)
    unbound-ihexp-sub (TUBFailedCast ub x x₁) ubt = TUBFailedCast (unbound-ihexp-sub ub ubt) (unbound-typ-sub x ubt) (unbound-typ-sub x₁ ubt)

    unbound-sub-sub : ∀{t τ σ} → tunbound-in-σ t σ → tunboundt-in t τ → tunbound-in-σ t (Sub[ τ / t ] σ)
    unbound-sub-sub TUBσId ubt = TUBσId
    unbound-sub-sub (TUBσSubst x ub) ubt = TUBσSubst (unbound-ihexp-sub x ubt) (unbound-sub-sub ub ubt)

  tbinderstt-disjoint-sym : ∀{τ τ'} → tbinderstt-disjoint τ τ' → tbinderstt-disjoint τ' τ
  tbinderstt-disjoint-sym tbd = {!   !}

  tbdΘ-extend : ∀{Θ t τ} → tbinders-disjoint-Θ Θ τ → tunboundt-in t τ → tbinders-disjoint-Θ (Θ ,, (t , <>)) τ
  tbdΘ-extend = {!   !}

  mutual
    lemma-tysubst-subst : ∀{Δ Θ Θ' Γ Γ' θ σ t τ} -> ∅ ⊢ τ wf ->
      tunbound-in-Δ t Δ → tunbound-in-Γ t Γ → tunboundt-in t τ → tunbound-in-σ t σ -> tbinders-disjoint-θ-σ θ σ → tbinders-unique-σ σ →
      Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' -> 
      Δ , Θ , Tctx[ τ / t ] Γ ⊢ TypSubst τ t θ , Sub[ τ / t ] σ :s: Θ' , (Tctx[ τ / t ] Γ')
    lemma-tysubst-subst {Γ = Γ} {Γ' = Γ'} wf ubd ubg tub ubs bd bu (STAIdId x tsub) = STASubst (STAIdId (lemma-map-elem-sub Γ Γ' x) tsub) wf 
    lemma-tysubst-subst {Γ = Γ} wf ubd ubg tub (TUBσSubst x₁ ubs) bd (TBUσSubst x₂ bu x₃) (STAIdSubst ts x alpha) = 
      lemma-typsubst-subst-comm (BDTθSubst (TUBσSubst (unbound-ihexp-sub x₁ tub) (unbound-sub-sub ubs tub)) BDTθId) (rewrite-gamma-subst (lem-map-extend-dist {Γ = Γ}) 
        (lemma-tysubst-subst wf ubd (lem-ub-extend (tunbound-ta-tunboundt x₁ ubd ubg x) ubg) tub ubs BDTθId bu {! ts !})) 
        (lemma-tysubst wf tub {!   !} {!   !} ubd ubg x₁ x₂ x)
    lemma-tysubst-subst {Θ = Θ} {σ = σ} wf ubd ubg tub ubs (BDTθSubst x₁ bd) bu (STASubst ts x) =
      lemma-typsubst-typsubst-comm (STASubst 
        (lemma-tysubst-subst wf ubd ubg tub ubs bd bu (rewrite-theta-subst (exchange-Θ {Θ = Θ}) ts)) x) 

    lemma-tysubst : ∀{ Δ Γ Θ d t τ1 τ2 } -> 
      ∅ ⊢ τ2 wf -> tunboundt-in t τ2 → tbinders-disjoint-Θ Θ τ2 → tbinderst-disjoint τ2 d →
      tunbound-in-Δ t Δ -> tunbound-in-Γ t Γ -> tunbound-in t d -> tbinders-unique d →
      Δ , (Θ ,, (t , <>)), Γ ⊢ d :: τ1 -> 
      Δ , Θ , Tctx[ τ2 / t ] Γ ⊢ (Ihexp[ τ2 / t ] d) :: Typ[ τ2 / t ] τ1
    lemma-tysubst _ _ _ _ _ _ _ _ TAConst = TAConst
    lemma-tysubst {Γ = Γ} {t = t} {τ1 = τ1} {τ2 = τ2} wf tub _ _ _ _ _ _ (TAVar {x = x} ing) = TAVar (lem-map-preserve-elem {Γ = Γ} ing)
    lemma-tysubst {Γ = Γ} wf tub tbdt (TBDTLam tbd tbtd) ubd ubg (TUBLam2 ub ub') (TBULam bu) (TALam x x₁ ta) = 
      TALam (lem-map-preserve-apart {Γ = Γ} x) 
      (wf-sub (BDTForall (tbinderstt-disjoint-sym tbtd) tub) (wf-closed wf tbdt) x₁ refl) -- (wf-closed wf) x₁ refl)
      (rewrite-gamma (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst wf tub tbdt tbd ubd (lem-ub-extend ub' ubg) ub bu ta))
    lemma-tysubst {Θ = Θ} {t = t} wf tub tbdt (TBDTTLam tbd x₂) ubd ubg (TUBTLam x ub) (TBUTLam bu x₁) (TATLam {t = t'} apt ta) with natEQ t t' | ctxindirect Θ t' 
    ... | Inr neq | Inr nint = TATLam nint (lemma-tysubst wf tub (tbdΘ-extend tbdt x₂) tbd ubd ubg ub bu (rewrite-theta (exchange-Θ {Θ = Θ}) ta))
    ... | _ | Inl (<> , int) rewrite int = abort (somenotnone apt)
    ... | Inl refl | Inr nint rewrite nint rewrite natEQrefl {t} = abort (somenotnone apt)
    lemma-tysubst wf tub tbdt (TBDTAp tbd tbd₁) ubd ubg (TUBAp ub1 ub2) (TBUAp bu bu₁ x) (TAAp ta ta' alpha) = TAAp (lemma-tysubst wf tub tbdt tbd ubd ubg ub1 bu ta) (lemma-tysubst wf tub tbdt tbd₁ ubd ubg ub2 bu₁ ta') (alpha-sub wf (lemma-alpha-forall alpha))
    lemma-tysubst {t = t} {τ2 = τ2} wf tub tbdt (TBDTTAp tbd x₁) ubd ubg (TUBTAp ubt ubt') (TBUTAp bu bu' bd) (TATAp {t = t'} {τ1 = τ1} {τ2 = τ4} {τ3 = τ3} x ta eq) with natEQ t t'
    ... | Inl refl rewrite natEQrefl {t'} rewrite natEQrefl {t} rewrite ! eq = TATAp {t = t'} {τ2 = τ4} (wf-sub (BDTForall (tbinderstt-disjoint-sym x₁) tub) (wf-closed wf tbdt) x refl)
                     (rewrite-typ (forall-sub-eq refl) (lemma-tysubst wf tub tbdt tbd ubd ubg ubt bu ta))
                     (lemma-typ-typ-1 τ4 wf)
    ... | Inr neq rewrite natEQneq neq rewrite ! eq with tunbound-ta-tunboundt ubt ubd ubg ta
    ...   | UBForall _ ub4 =
       TATAp {t = t'} {τ2 = Typ[ τ2 / t ] τ4} (wf-sub (BDTForall (tbinderstt-disjoint-sym x₁) tub) (wf-closed wf tbdt) x refl)
                    (rewrite-typ (forall-sub-neq neq) (lemma-tysubst wf tub tbdt tbd ubd ubg ubt bu ta))
                    (lemma-typ-typ-2 τ4 ub4 wf neq)
    lemma-tysubst wf tub tbdt tbd ubd ubg (TUBHole x₁ x₂) (TBUEHole x₃ x₄ x₅) (TAEHole x ts eq eq') rewrite eq rewrite eq' = 
      TAEHole x (lemma-tysubst-subst wf ubd ubg tub x₂ x₅ x₄ ts) refl refl
    lemma-tysubst wf tub tbdt (TBDTNEHole x₂ tbd) ubd ubg (TUBNEHole x₁ ubs ub) (TBUNEHole bu but bus bdts) (TANEHole x ta ts eq eq') rewrite eq rewrite eq' = TANEHole x (lemma-tysubst wf tub tbdt tbd ubd ubg ub bu ta) (lemma-tysubst-subst wf ubd ubg tub ubs bdts bus ts) refl refl
    lemma-tysubst wf tub tbdt (TBDTCast tbd x₃ x₄) ubd ubg (TUBCast ub x₁ x₂) (TBUCast bu bd1 bd2) (TACast ta x x~ alpha) = TACast (lemma-tysubst wf tub tbdt tbd ubd ubg ub bu ta) (wf-sub (BDTForall x₄ tub) (wf-closed wf tbdt) x refl) (~Typ[] wf x₁ x₂ x~) (alpha-sub wf (lemma-alpha-forall alpha))
    lemma-tysubst wf tub tbdt (TBDTFailedCast tbd x₃ x₄) ubd ubg (TUBFailedCast ub x₁ x₂) (TBUFailedCast bu _ _) (TAFailedCast ta tgnd tgnd' x alpha) = TAFailedCast (lemma-tysubst wf tub tbdt tbd ubd ubg ub bu ta) (ground-subst tgnd) (ground-subst tgnd') (λ eq → x (foo tgnd tgnd' eq)) (alpha-sub wf (lemma-alpha-forall alpha))
      where
        foo : ∀{t1 t2 t3 t} -> t1 ground -> t2 ground -> Typ[ t3 / t ] t1 ~ Typ[ t3 / t ] t2 -> t1 ~ t2
        foo {t1} {t2} {t3} {t} g1 g2 eq rewrite ground-subst-id {t} {t1} {t3} g1 rewrite ground-subst-id {t} {t2} {t3} g2 = eq
  