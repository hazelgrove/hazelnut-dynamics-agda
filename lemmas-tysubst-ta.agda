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

  rewrite-codomain-in : ∀{t : htyp} {t' x Γ} -> t == t' -> (x , t) ∈ Γ -> (x , t') ∈ Γ
  rewrite-codomain-in eq p rewrite eq = p

  lem-sub-ub : ∀{t t' τ τ''} → (τ' : htyp) → tunboundt-in t τ' → tunboundt-in t τ'' → Typ[ τ'' / t' ] τ' == τ → tunboundt-in t τ
  lem-sub-ub b ub1 ub2 eq rewrite ! eq = ub1
  lem-sub-ub {t' = t'} (T x) ub1 ub2 eq with natEQ t' x
  ... | Inl refl rewrite eq = ub2
  ... | Inr neq rewrite ! eq = ub1
  lem-sub-ub ⦇-⦈ ub1 ub2 eq rewrite ! eq = ub1
  lem-sub-ub (τ' ==> τ'') (UBArr ub1 ub3) ub2 eq rewrite ! eq = UBArr (lem-sub-ub τ' ub1 ub2 refl) (lem-sub-ub τ'' ub3 ub2 refl)
  lem-sub-ub {t' = t'} (·∀ x τ') (UBForall ne ub1) ub2 eq with natEQ t' x
  ... | Inl refl rewrite ! eq = UBForall ne ub1
  ... | Inr neq rewrite ! eq = UBForall ne (lem-sub-ub τ' ub1 ub2 refl)

  lem-ub-extend : ∀{x t τ Γ} → tunboundt-in t τ → tunbound-in-Γ t Γ → tunbound-in-Γ t (Γ ,, (x , τ))
  lem-ub-extend {x} {t} {τ} {Γ} ubt (UBΓ ubg) = UBΓ foo
    where
      foo : (x' : Nat) -> (τ' : htyp) -> (x' , τ') ∈ (Γ ,, (x , τ)) -> tunboundt-in t τ'
      foo x' τ' mem with ctxindirect Γ x'
      ... | Inl (τ'' , ing) rewrite ing rewrite ! (someinj mem) = ubg x' τ'' ing
      ... | Inr nig rewrite nig with natEQ x x'
      ...   | Inl refl rewrite someinj mem = ubt
      ...   | Inr neq = abort (somenotnone (! mem))

  lem-sub-sub-ub : ∀{t τ θ} → (τ' : htyp) → tunboundt-in t τ' → tunbound-in-θ t θ → apply-typenv θ τ' == τ → tunboundt-in t τ
  lem-sub-sub-ub τ' ub UBθId eq rewrite eq = ub
  lem-sub-sub-ub τ' ub (UBθSubst {θ = θ} x ubth) eq = lem-sub-ub (apply-typenv θ τ') (lem-sub-sub-ub τ' ub ubth refl) x eq

  tunbound-ta-tunboundt : ∀{Δ Θ Γ d t τ} → tunbound-in t d → tunbound-in-Δ t Δ → tunbound-in-Γ t Γ → Δ , Θ , Γ ⊢ d :: τ → tunboundt-in t τ
  tunbound-ta-tunboundt ub ubd ubg TAConst = UBBase
  tunbound-ta-tunboundt {τ = τ} TUBVar ubd (UBΓ ubg) (TAVar {x = y} x) = ubg y τ x
  tunbound-ta-tunboundt (TUBLam2 ub ubt) ubd ubg (TALam x x₁ ta) = UBArr ubt (tunbound-ta-tunboundt ub ubd (lem-ub-extend ubt ubg) ta)
  tunbound-ta-tunboundt (TUBTLam x₁ ub) ubd ubg (TATLam x ta) = UBForall x₁ (tunbound-ta-tunboundt ub ubd ubg ta)
  tunbound-ta-tunboundt (TUBAp ub1 ub2) ubd ubg (TAAp ta ta₁) with tunbound-ta-tunboundt ub1 ubd ubg ta
  ... | UBArr _ ubt2 = ubt2
  tunbound-ta-tunboundt (TUBTAp ub ubt) ubd ubg (TATAp x ta eq) with tunbound-ta-tunboundt ub ubd ubg ta
  ... | UBForall ub' ubt' = lem-sub-ub _ ubt' ubt eq
  tunbound-ta-tunboundt (TUBHole ubt ubs) (UBΔ ubd) ubg (TAEHole {u = u} {Θ' = Θ'} {Γ' = Γ'} {τ' = τ'} x x₁ x₂ x₃) = let ubt' = ubd u Θ' Γ' τ' x in
    lem-sub-sub-ub τ' ubt' ubt (! x₂)
  tunbound-ta-tunboundt (TUBNEHole ubt ubs ub) (UBΔ ubd) ubg (TANEHole {u = u} {Θ' = Θ'} {Γ' = Γ'} {τ' = τ'} x ta x₁ x₂ x₃) = let ubt' = ubd u Θ' Γ' τ' x in
    lem-sub-sub-ub τ' ubt' ubt (! x₂)
  tunbound-ta-tunboundt (TUBCast ub ubt1 ubt2) ubd ubg (TACast ta x x₁) = ubt2
  tunbound-ta-tunboundt (TUBFailedCast ub ubt1 ubt2) ubd ubg (TAFailedCast ta x x₁ x₂) = ubt2

{-
  wf-unbound-tfresht : ∀{t τ Θ} -> t # Θ -> Θ ⊢ τ wf -> tunboundt-in t τ -> tfresht t τ
  wf-unbound-tfresht {τ = b} apt wf ub = TFBase
  wf-unbound-tfresht {t} {τ = T x} apt (WFVar int) UBTVar with natEQ t x 
  ... | Inl refl = TFTVar (abort (somenotnone ((! int) · apt)))
  ... | Inr neq = TFTVar neq
  wf-unbound-tfresht {τ = ⦇-⦈} apt wf ub = TFHole
  wf-unbound-tfresht {τ = τ ==> τ₁} apt (WFArr wf1 wf2) (UBArr ub1 ub2) = TFArr (wf-unbound-tfresht apt wf1 ub1) (wf-unbound-tfresht apt wf2 ub2)
  wf-unbound-tfresht {τ = ·∀ x τ} {Θ = Θ} apt (WFForall wf) (UBForall ne ub) = TFForall ne (wf-unbound-tfresht (lem-apart-extend {Γ = Θ} apt ne) wf ub)
-}

  lemma-typsubst-typsubst-comm : ∀{t1 t2 τ1 τ2 Δ Θ Θ' Γ Γ' θ σ} → Δ , Θ , Γ ⊢ TypSubst τ1 t1 (TypSubst τ2 t2 θ) , σ :s: Θ' , Γ'
    → Δ , Θ , Γ ⊢ TypSubst τ2 t2 (TypSubst τ1 t1 θ) , σ :s: Θ' , Γ'
  lemma-typsubst-typsubst-comm {Θ = Θ} (STASubst (STASubst ts x₁) x) = STASubst (STASubst (rewrite-theta-subst (exchange-Θ {Θ = Θ}) ts) x) x₁

  mutual
    lemma-typsubst-subst-comm : ∀{Δ Θ Θ' Γ Γ' t τ τ' d y θ σ} →
      tbinders-disjoint-θ-σ (TypSubst τ' t θ) (Subst d y σ) →
      Δ , Θ , (Γ ,, (y , τ))  ⊢ TypSubst τ' t θ , σ :s: Θ' , Γ' →
      Δ , Θ , Γ ⊢ d :: τ →
      Δ , Θ , Γ ⊢ TypSubst τ' t θ , Subst d y σ :s: Θ' , Γ'
    lemma-typsubst-subst-comm (BDTθSubst (TUBσSubst x₂ x₃) ub) (STASubst (STAIdId x x₁) wf) ta = STASubst (STAIdSubst (STAIdId x x₁) (weaken-ta-typ2 x₂ ta)) wf
    lemma-typsubst-subst-comm (BDTθSubst (TUBσSubst x₂ x₃) ub) (STASubst (STAIdSubst ts x) wf) ta = STASubst (lemma-subst-comm ub (STAIdSubst ts x) (weaken-ta-typ2 x₂ ta)) wf
    lemma-typsubst-subst-comm (BDTθSubst (TUBσSubst x₂ x₃) ub) (STASubst (STASubst ts x) wf) ta = STASubst (lemma-typsubst-subst-comm ub (STASubst ts x) (weaken-ta-typ2 x₂ ta)) wf
    
    lemma-subst-comm : ∀{Δ Θ Θ' Γ Γ' τ d y θ σ} →
      tbinders-disjoint-θ-σ θ (Subst d y σ) →
      Δ , Θ , (Γ ,, (y , τ))  ⊢ θ , σ :s: Θ' , Γ' →
      Δ , Θ , Γ ⊢ d :: τ →
      Δ , Θ , Γ ⊢ θ , Subst d y σ :s: Θ' , Γ'
    lemma-subst-comm {Δ} {Θ} {.Θ₁} {Γ} {Γ'} {τ} {d} {y} {TypId Θ₁} {.(Id Γ')} bd (STAIdId x x₁) ta = STAIdSubst (STAIdId x x₁) ta
    lemma-subst-comm {Δ} {Θ} {.Θ₁} {Γ} {Γ'} {τ} {d} {y} {TypId Θ₁} {.(Subst _ _ _)} bd (STAIdSubst ts x) ta = STAIdSubst (STAIdSubst ts x) ta
    lemma-subst-comm {Δ} {Θ} {Θ'} {Γ} {Γ'} {τ} {d} {y} {TypSubst τ₁ t θ} {σ} (BDTθSubst (TUBσSubst x x₁) bd) ts ta = lemma-typsubst-subst-comm (BDTθSubst (TUBσSubst x x₁) bd) ts ta

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

  lemma-typ-typ-2 : ∀{τ1 τ2 t t'} → (τ : htyp) → tunboundt-in t (Typ[ τ1 / t' ] τ) → ∅ ⊢ τ2 wf → t ≠ t' → Typ[ Typ[ τ2 / t ] τ1 / t' ] (Typ[ τ2 / t ] τ) == Typ[ τ2 / t ] (Typ[ τ1 / t' ] τ)
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

  mutual
    lemma-tysubst-subst : ∀{Δ Θ Θ' Γ Γ' θ σ t τ} -> ∅ ⊢ τ wf ->
      tunbound-in-Δ t Δ → tunbound-in-Γ t Γ → tunboundt-in t τ → tunbound-in-σ t σ -> tbinders-disjoint-θ-σ θ σ → tbinders-unique-σ σ →
      Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' -> 
      Δ , Θ , Tctx[ τ / t ] Γ ⊢ TypSubst τ t θ , Sub[ τ / t ] σ :s: Θ' , (Tctx[ τ / t ] Γ')
    lemma-tysubst-subst {Γ = Γ} {Γ' = Γ'} wf ubd ubg tub ubs bd bu (STAIdId x tsub) = STASubst (STAIdId (lemma-map-elem-sub Γ Γ' x) tsub) wf 
    lemma-tysubst-subst {Γ = Γ} wf ubd ubg tub (TUBσSubst x₁ ubs) bd (TBUσSubst x₂ bu x₃) (STAIdSubst ts x) = 
      lemma-typsubst-subst-comm (BDTθSubst (TUBσSubst (unbound-ihexp-sub x₁ tub) (unbound-sub-sub ubs tub)) BDTθId) (rewrite-gamma-subst (lem-map-extend-dist {Γ = Γ}) 
        (lemma-tysubst-subst wf ubd (lem-ub-extend (tunbound-ta-tunboundt x₁ ubd ubg x) ubg) tub ubs BDTθId bu ts)) 
        (lemma-tysubst wf ubd ubg x₁ x₂ x)
    lemma-tysubst-subst {Θ = Θ} {σ = σ} wf ubd ubg tub ubs (BDTθSubst x₁ bd) bu (STASubst ts x) =
      lemma-typsubst-typsubst-comm (STASubst 
        (lemma-tysubst-subst wf ubd ubg tub ubs bd bu (rewrite-theta-subst (exchange-Θ {Θ = Θ}) ts)) x) 

    lemma-tysubst : ∀{ Δ Γ Θ d t τ1 τ2 } -> 
      ∅ ⊢ τ2 wf -> tunbound-in-Δ t Δ -> tunbound-in-Γ t Γ -> tunbound-in t d -> tbinders-unique d →
      Δ , (Θ ,, (t , <>)), Γ ⊢ d :: τ1 -> 
      Δ , Θ , Tctx[ τ2 / t ] Γ ⊢ (Ihexp[ τ2 / t ] d) :: Typ[ τ2 / t ] τ1
    lemma-tysubst _ _ _ _ _ TAConst = TAConst
    lemma-tysubst {Γ = Γ} {t = t} {τ1 = τ1} {τ2 = τ2} wf _ _ _ _ (TAVar {x = x} ing) = TAVar (lem-map-preserve-elem {Γ = Γ} ing)
    lemma-tysubst {Γ = Γ} wf ubd ubg (TUBLam2 ub ub') (TBULam bu) (TALam x x₁ ta) = 
      TALam (lem-map-preserve-apart {Γ = Γ} x) 
      (wf-sub (wf-closed wf) x₁ refl)
      (rewrite-gamma (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst wf ubd (lem-ub-extend ub' ubg) ub bu ta))
    lemma-tysubst {Θ = Θ} {t = t} wf ubd ubg (TUBTLam x ub) (TBUTLam bu x₁) (TATLam {t = t'} apt ta) with natEQ t t' | ctxindirect Θ t' 
    ... | Inr neq | Inr nint = TATLam nint (lemma-tysubst wf ubd ubg ub bu (rewrite-theta (exchange-Θ {Θ = Θ}) ta))
    ... | _ | Inl (<> , int) rewrite int = abort (somenotnone apt)
    ... | Inl refl | Inr nint rewrite nint rewrite natEQrefl {t} = abort (somenotnone apt)
    lemma-tysubst wf ubd ubg (TUBAp ub1 ub2) (TBUAp bu bu₁ x) (TAAp ta ta') = TAAp (lemma-tysubst wf ubd ubg ub1 bu ta) (lemma-tysubst wf ubd ubg ub2 bu₁ ta')
    lemma-tysubst {t = t} {τ2 = τ2} wf ubd ubg (TUBTAp ubt ubt') (TBUTAp bu _ _) (TATAp {t = t'} {τ1 = τ1} {τ2 = τ4} {τ3 = τ3} x ta eq) with natEQ t t'
    ... | Inl refl rewrite natEQrefl {t'} rewrite natEQrefl {t} rewrite ! eq = TATAp {t = t'} {τ2 = τ4} ((wf-sub (wf-closed wf) x refl))
                     (rewrite-typ (forall-sub-eq refl) (lemma-tysubst wf ubd ubg ubt bu ta))
                     (lemma-typ-typ-1 τ4 wf)
    ... | Inr neq rewrite natEQneq neq rewrite ! eq with tunbound-ta-tunboundt ubt ubd ubg ta
    ...   | UBForall _ ub4 =
       TATAp {t = t'} {τ2 = Typ[ τ2 / t ] τ4} (wf-sub (wf-closed wf) x refl)
                    (rewrite-typ (forall-sub-neq neq) (lemma-tysubst wf ubd ubg ubt bu ta))
                    (lemma-typ-typ-2 τ4 (lem-sub-ub τ4 ub4 ubt' refl) wf neq)
    lemma-tysubst wf ubd ubg (TUBHole x₁ x₂) (TBUEHole x₃ x₄ x₅) (TAEHole x ts eq eq') rewrite eq rewrite eq' = 
      TAEHole x (lemma-tysubst-subst wf ubd ubg {!   !} x₂ x₅ x₄ ts) refl refl
    lemma-tysubst wf ubd ubg (TUBNEHole x₁ ubs ub) (TBUNEHole bu but bus bdts) (TANEHole x ta ts eq eq') rewrite eq rewrite eq' = TANEHole x (lemma-tysubst wf ubd ubg ub bu ta) (lemma-tysubst-subst wf ubd ubg {!   !} ubs bdts bus ts) refl refl
    lemma-tysubst wf ubd ubg (TUBCast ub x₁ x₂) (TBUCast bu) (TACast ta x x~) = TACast (lemma-tysubst wf ubd ubg ub bu ta) ((wf-sub (wf-closed wf) x refl)) (~Typ[] wf x₁ x₂ x~)
    lemma-tysubst wf ubd ubg (TUBFailedCast ub x₁ x₂) (TBUFailedCast bu) (TAFailedCast ta tgnd tgnd' x) = TAFailedCast (lemma-tysubst wf ubd ubg ub bu ta) (ground-subst tgnd) (ground-subst tgnd') 
      λ eq → x (foo tgnd tgnd' eq)
      where
        foo : ∀{t1 t2 t3 t} -> t1 ground -> t2 ground -> Typ[ t3 / t ] t1 ~ Typ[ t3 / t ] t2 -> t1 ~ t2
        foo {t1} {t2} {t3} {t} g1 g2 eq rewrite ground-subst-id {t} {t1} {t3} g1 rewrite ground-subst-id {t} {t2} {t3} g2 = eq
           