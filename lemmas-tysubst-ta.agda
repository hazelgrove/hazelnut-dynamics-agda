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

  tunbound-ta-tunboundt : ∀{Δ Θ Γ d t τ} → tunbound-in t d → tunbound-in-Δ t Δ → tunbound-in-Γ t Γ → Δ , Θ , Γ ⊢ d :: τ → tunboundt-in t τ
  tunbound-ta-tunboundt ub ubd ubg TAConst = UBBase
  tunbound-ta-tunboundt {τ = τ} TUBVar ubd (UBΓ ubg) (TAVar {x = y} x) = ubg y τ x
  tunbound-ta-tunboundt (TUBLam2 ub ubt) ubd ubg (TALam x x₁ ta) = UBArr ubt (tunbound-ta-tunboundt ub ubd {!   !} ta)
  tunbound-ta-tunboundt (TUBTLam x₁ ub) ubd ubg (TATLam x ta) = UBForall x₁ (tunbound-ta-tunboundt ub ubd ubg ta)
  tunbound-ta-tunboundt (TUBAp ub1 ub2) ubd ubg (TAAp ta ta₁) with tunbound-ta-tunboundt ub1 ubd ubg ta
  ... | UBArr _ ubt2 = ubt2
  tunbound-ta-tunboundt (TUBTAp ub ubt) ubd ubg (TATAp x ta eq) with tunbound-ta-tunboundt ub ubd ubg ta
  ... | UBForall ub' ubt' = lem-sub-ub _ ubt' ubt eq
  tunbound-ta-tunboundt (TUBHole ubt) (UBΔ ubd) ubg (TAEHole {u = u} {Θ' = Θ'} {Γ' = Γ'} {τ' = τ'} x x₁ x₂ x₃) = let ubt' = ubd u Θ' Γ' τ' x in {!   !}
  tunbound-ta-tunboundt (TUBNEHole x₄ ub) (UBΔ ubd) ubg (TANEHole x ta x₁ x₂ x₃) = {!   !}
  tunbound-ta-tunboundt (TUBCast ub ubt1 ubt2) ubd ubg (TACast ta x x₁) = ubt2
  tunbound-ta-tunboundt (TUBFailedCast ub ubt1 ubt2) ubd ubg (TAFailedCast ta x x₁ x₂) = ubt2

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
  binders-tenvtfresh {Θ = Θ} (STASubst ts x) apt (UBθSubst x₁ ub x₂) (BUθSubst x₃ bu x₄) = {!   !} -- TETFSubst (wf-unbound-tfresht apt x x₁) (binders-tenvtfresh ts (lem-apart-extend {Γ = Θ} apt x₂) ub bu) x₂

  lemma-typsubst-typsubst-comm : ∀{t1 t2 τ1 τ2 Δ Θ Θ' Γ Γ' θ σ} → Δ , Θ , Γ ⊢ TypSubst τ1 t1 (TypSubst τ2 t2 θ) , σ :s: Θ' , Γ'
    → Δ , Θ , Γ ⊢ TypSubst τ2 t2 (TypSubst τ1 t1 θ) , σ :s: Θ' , Γ'
  lemma-typsubst-typsubst-comm {Θ = Θ} (STASubst (STASubst ts x₁) x) = {!   !} -- STASubst (STASubst (rewrite-theta-subst (exchange-Θ {Θ = Θ}) ts) (weaken-t-wf x)) wf

  lemma-typsubst-subst-comm : ∀{Δ Θ Θ' Γ Γ' t τ τ' d y θ σ} →
    Δ , Θ , (Γ ,, (y , τ))  ⊢ TypSubst τ' t θ , σ :s: Θ' , Γ' →
    Δ , Θ , Γ ⊢ d :: τ →
    Δ , Θ , Γ ⊢ TypSubst τ' t θ , Subst d y σ :s: Θ' , Γ'
  lemma-typsubst-subst-comm = {!   !}
{-
  lemma-typsubst-subst-comm {θ = TypId Θ} (STASubst (STAIdId gammasub thetasub) x) ta = STASubst (STAIdSubst (STAIdId gammasub thetasub) (weaken-ta-typ ta)) x
  lemma-typsubst-subst-comm {θ = TypId Θ} (STASubst (STAIdSubst ts ta) x) ta' = STASubst (STAIdSubst (STAIdSubst ts ta) (weaken-ta-typ ta')) x
  lemma-typsubst-subst-comm {θ = TypSubst τ t θ} (STASubst {τ = τ'} (STASubst ts x₁) x) ta = 
    STASubst (lemma-typsubst-subst-comm (STASubst ts x₁) (weaken-ta-typ ta)) x
-}

  lemma-subst-comm : ∀{Δ Θ Θ' Γ Γ' τ d y θ σ} →
    Δ , Θ , (Γ ,, (y , τ))  ⊢ θ , σ :s: Θ' , Γ' →
    Δ , Θ , Γ ⊢ d :: τ →
    Δ , Θ , Γ ⊢ θ , Subst d y σ :s: Θ' , Γ'
  lemma-subst-comm {Δ} {Θ} {.Θ₁} {Γ} {Γ'} {τ} {d} {y} {TypId Θ₁} {.(Id Γ')} (STAIdId x x₁) ta = STAIdSubst (STAIdId x x₁) {! ta !}
  lemma-subst-comm {Δ} {Θ} {.Θ₁} {Γ} {Γ'} {τ} {d} {y} {TypId Θ₁} {.(Subst _ _ _)} (STAIdSubst ts x) ta = STAIdSubst (STAIdSubst ts x) {! ta !}
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

  mutual
    lemma-strengthen-subst-typ : ∀{Δ Θ Θ' Γ Γ' θ σ t} -> tenvtfresh t θ -> Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' -> Δ , Θ , Γ ⊢ θ , σ :s: Θ' , Γ'
    lemma-strengthen-subst-typ ef ts = {!!}

    lemma-tysubst-subst : ∀{Δ Θ Θ' Γ Γ' θ σ t τ} -> ∅ ⊢ τ wf ->
      Δ , (Θ ,, (t , <>)) , Γ ⊢ θ , σ :s: Θ' , Γ' -> 
      Δ , Θ , Tctx[ τ / t ] Γ ⊢ TypSubst τ t θ , Sub[ τ / t ] σ :s: Θ' , (Tctx[ τ / t ] Γ')
    lemma-tysubst-subst {Γ = Γ} {Γ' = Γ'} wf (STAIdId x tsub) = STASubst (STAIdId (lemma-map-elem-sub Γ Γ' x) tsub) wf 
    lemma-tysubst-subst {Γ = Γ} wf (STAIdSubst ts x) = lemma-typsubst-subst-comm (rewrite-gamma-subst (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst-subst wf ts)) ((lemma-tysubst wf {!   !} {!   !} {! x !})) 
    lemma-tysubst-subst {Θ = Θ} {σ = σ} wf (STASubst ts x) = lemma-typsubst-typsubst-comm (STASubst (lemma-tysubst-subst wf (rewrite-theta-subst (exchange-Θ {Θ = Θ}) ts)) x) 

    lemma-tysubst : ∀{ Δ Γ Θ d t τ1 τ2 } -> 
      ∅ ⊢ τ2 wf -> tunbound-in t d -> tunboundt-in t τ1 -> 
      Δ , (Θ ,, (t , <>)), Γ ⊢ d :: τ1 -> 
      Δ , Θ , Tctx[ τ2 / t ] Γ ⊢ (Ihexp[ τ2 / t ] d) :: Typ[ τ2 / t ] τ1
    lemma-tysubst _ _ _ TAConst = TAConst
    lemma-tysubst {Γ = Γ} {t = t} {τ1 = τ1} {τ2 = τ2} wf _ _ (TAVar {x = x} ing) = TAVar (lem-map-preserve-elem {Γ = Γ} ing)
    lemma-tysubst {Γ = Γ} wf ub (UBArr ubt1 ubt2) (TALam x x₁ ta) = 
      TALam (lem-map-preserve-apart {Γ = Γ} x) 
      (wf-sub (wf-closed wf) x₁ refl)
      (rewrite-gamma (lem-map-extend-dist {Γ = Γ}) (lemma-tysubst wf {!   !} ubt2 ta))
    lemma-tysubst {Θ = Θ} {t = t} wf ub (UBForall neq ubt) (TATLam {t = t'} apt ta) with natEQ t t' | ctxindirect Θ t' 
    ... | Inr neq | Inr nint = TATLam nint (lemma-tysubst wf {!   !} ubt (rewrite-theta (exchange-Θ {Θ = Θ}) ta))
    ... | _ | Inl (<> , int) rewrite int = abort (somenotnone apt)
    ... | Inl refl | Inr nint rewrite nint rewrite natEQrefl {t} = abort (somenotnone apt)
    lemma-tysubst wf (TUBAp ub1 ub2) ubt (TAAp ta ta') = TAAp (lemma-tysubst wf {!   !} (UBArr {!   !} ubt) ta) (lemma-tysubst wf {!   !} {! ub !} ta')
    lemma-tysubst {t = t} {τ2 = τ2} wf ub ubt (TATAp {t = t'} {τ1 = τ1} {τ2 = τ4} {τ3 = τ3} x ta eq) with natEQ t t'
    ... | Inl refl rewrite natEQrefl {t'} rewrite natEQrefl {t} rewrite ! eq = TATAp {t = t'} {τ2 = τ4} ((wf-sub (wf-closed wf) x refl))
                     (rewrite-typ (forall-sub-eq refl) (lemma-tysubst wf {!   !} {!   !} ta))
                     (lemma-typ-typ-1 τ4 wf)
    ... | Inr neq rewrite natEQneq neq rewrite ! eq =  TATAp {t = t'} {τ2 = Typ[ τ2 / t ] τ4} (wf-sub (wf-closed wf) x refl)
                    (rewrite-typ (forall-sub-neq neq) (lemma-tysubst wf {!   !} {!   !} ta))
                    (lemma-typ-typ-2 τ4 ubt wf neq)
    lemma-tysubst wf ub ubt (TAEHole x ts eq eq') rewrite eq rewrite eq' = 
      TAEHole x (lemma-tysubst-subst wf ts) refl refl
    lemma-tysubst wf ub ubt (TANEHole x ta ts eq eq') rewrite eq rewrite eq' = TANEHole x (lemma-tysubst wf {!   !} {!   !} ta) (lemma-tysubst-subst wf ts) refl refl
    lemma-tysubst wf ub ubt (TACast ta x x~) = TACast (lemma-tysubst wf {!   !} {!   !} ta) ((wf-sub (wf-closed wf) x refl)) {! (~Typ[] x~) !}
    lemma-tysubst wf ub ubt (TAFailedCast ta tgnd tgnd' x) = TAFailedCast (lemma-tysubst wf {!   !} {!   !} ta) (ground-subst tgnd) (ground-subst tgnd') 
      λ eq → x (foo tgnd tgnd' eq)
      where
        foo : ∀{t1 t2 t3 t} -> t1 ground -> t2 ground -> Typ[ t3 / t ] t1 ~ Typ[ t3 / t ] t2 -> t1 ~ t2
        foo {t1} {t2} {t3} {t} g1 g2 eq rewrite ground-subst-id {t} {t1} {t3} g1 rewrite ground-subst-id {t} {t2} {t3} g2 = eq
           