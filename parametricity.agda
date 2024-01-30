open import Nat
open import Prelude
open import core
open alpha
open import lemmas-alpha

open import contexts

module parametricity where

  -- Note from Thomas: There may be trouble here with whether casts can vary
  -- under =0. If they can, equivalent expressions can be stuck or unstuck.
  -- If they can't, then as equivalent expressions evaluate some may fail the 
  -- casts and some may succeed? Or perhaps I haven't taken sufficient advantage
  -- of the premimses. 

  -- Disallow casts from varying. Prove lemma that if we elaborate a well-typed
  -- complete program, all casts are identity casts.

  -- The other open issue is about the types attached to holes. Can they vary?
  -- The lemma about =0 respecting substitution requires they be able to vary. 

  data _=0_ : (d1 d2 : ihexp) → Set where 
    Eq0Const : c =0 c
    Eq0Var : ∀{x} → (X x) =0 (X x) 
    Eq0EHole : ∀{u} → ⦇-⦈⟨ u ⟩ =0 ⦇-⦈⟨ u ⟩
    Eq0Lam : ∀{x d1 d2 τ1 τ2} → d1 =0 d2 → (·λ x [ τ1 ] d1) =0 (·λ x [ τ2 ] d2)
    Eq0TLam : ∀{t d1 d2} → d1 =0 d2 → (·Λ t d1) =0 (·Λ t d2)
    Eq0NEHole : ∀{u d1 d2} → d1 =0 d2 →  (⦇⌜ d1 ⌟⦈⟨ u ⟩) =0 (⦇⌜ d2 ⌟⦈⟨ u ⟩)
    Eq0Ap :  ∀{d1 d2 d3 d4} → d1 =0 d3 →  d2 =0 d4 →  (d1 ∘ d2) =0 (d3 ∘ d4)
    Eq0TAp : ∀{d1 d2 τ1 τ2} → d1 =0 d2 → (d1 < τ1 >) =0 (d2 < τ2 >)
    Eq0Cast : ∀{d1 d2 τ1 τ2} → d1 =0 d2 → (d1 ⟨ τ1 ⇒ τ2 ⟩) =0 (d2 ⟨ τ1 ⇒ τ2 ⟩)
    Eq0FailedCast : ∀{d1 d2 τ1 τ2} → d1 =0 d2 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0 (d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  data _=0ε_ : (ε1 ε2 : ectx) → Set where 
    Eq0Dot : ⊙ =0ε ⊙
    Eq0Ap1 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε ε2) → (d1 =0 d2) → (ε1 ∘₁ d1) =0ε (ε2 ∘₁ d2)
    Eq0Ap2 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε ε2) → (d1 =0 d2) → (d1 ∘₂ ε1) =0ε (d2 ∘₂ ε2)
    Eq0TAp : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε ε2) → (ε1 < τ1 >) =0ε (ε2 < τ2 >)
    Eq0NEHole : ∀{ε1 ε2 u} → (ε1 =0ε ε2) → (⦇⌜ ε1 ⌟⦈⟨ u ⟩) =0ε (⦇⌜ ε2 ⌟⦈⟨ u ⟩)
    Eq0Cast : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε ε2) → (ε1 ⟨ τ1 ⇒ τ2 ⟩) =0ε (ε2 ⟨ τ1 ⇒ τ2 ⟩)
    Eq0FailedCast : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε ε2) → (ε1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0ε (ε2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  eq0-refl : ∀{d : ihexp} → d =0 d
  eq0-refl {d = c} = Eq0Const
  eq0-refl {d = X x} = Eq0Var
  eq0-refl {d = ·λ x [ x₁ ] d} = Eq0Lam eq0-refl
  eq0-refl {d = ·Λ x d} = Eq0TLam eq0-refl
  eq0-refl {d = ⦇-⦈⟨ x ⟩} = Eq0EHole
  eq0-refl {d = ⦇⌜ d ⌟⦈⟨ x ⟩} = Eq0NEHole eq0-refl
  eq0-refl {d = d ∘ d₁} = Eq0Ap eq0-refl eq0-refl
  eq0-refl {d = d < x >} = Eq0TAp eq0-refl
  eq0-refl {d = d ⟨ x ⇒ x₁ ⟩} = Eq0Cast eq0-refl
  eq0-refl {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} = Eq0FailedCast eq0-refl

  eq0ε-refl : ∀{ε : ectx} → ε =0ε ε
  eq0ε-refl {ε = ⊙} = Eq0Dot
  eq0ε-refl {ε = ε ∘₁ x} = Eq0Ap1 eq0ε-refl eq0-refl
  eq0ε-refl {ε = x ∘₂ ε} = Eq0Ap2 eq0ε-refl eq0-refl
  eq0ε-refl {ε = ε < x >} = Eq0TAp eq0ε-refl
  eq0ε-refl {ε = ⦇⌜ ε ⌟⦈⟨ x ⟩} = Eq0NEHole eq0ε-refl
  eq0ε-refl {ε = ε ⟨ x ⇒ x₁ ⟩} = Eq0Cast eq0ε-refl
  eq0ε-refl {ε = ε ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} = Eq0FailedCast eq0ε-refl

  eq0-boxedval : 
    ∀ {d1 d2} →
    d1 =0 d2 →
    d1 boxedval →
    d2 boxedval
  eq0-boxedval Eq0Const bv = bv
  eq0-boxedval Eq0EHole bv = bv
  eq0-boxedval Eq0Var bv = bv
  eq0-boxedval (Eq0Lam eq) bv = BVVal VLam
  eq0-boxedval (Eq0TLam eq) bv = BVVal VTLam
  eq0-boxedval (Eq0NEHole eq) (BVVal ())
  eq0-boxedval (Eq0Ap eq eq₁) (BVVal ())
  eq0-boxedval (Eq0TAp eq) (BVVal ())
  eq0-boxedval (Eq0Cast eq) (BVArrCast x bv) = BVArrCast x (eq0-boxedval eq bv)
  eq0-boxedval (Eq0Cast eq) (BVForallCast x bv) = BVForallCast x (eq0-boxedval eq bv)
  eq0-boxedval (Eq0Cast eq) (BVHoleCast x bv) = BVHoleCast x (eq0-boxedval eq bv)
  eq0-boxedval (Eq0FailedCast eq) (BVVal ())

  eq0-subst : 
    ∀ {x d1 d2} →
    (d3 d4 : ihexp) →
    d1 =0 d2 →
    d3 =0 d4 →
    ([ d1 / x ] d3) =0 ([ d2 / x ] d4)
  eq0-subst c c _ Eq0Const = Eq0Const
  eq0-subst {x = x} (X y) (X y) eq Eq0Var with natEQ y x
  ... | Inl refl = eq
  ... | Inr x = eq0-refl
  eq0-subst {x = x} (·λ y [ τ ] d3) (·λ y [ τ1 ] d4) eq1 (Eq0Lam eq2) -- (Eq0Lam eq2)
    with natEQ y x
  ... | Inl refl = Eq0Lam eq2
  ... | Inr x = Eq0Lam (eq0-subst d3 d4 eq1 eq2)
  eq0-subst (·Λ x d3) (·Λ x d4) eq1 (Eq0TLam eq2) with eq0-subst d3 d4 eq1 eq2 
  ... | eq3 = Eq0TLam eq3
  eq0-subst ⦇-⦈⟨ x ⟩ ⦇-⦈⟨ x ⟩ eq1 Eq0EHole = {!  !}
  eq0-subst ⦇⌜ d3 ⌟⦈⟨ x ⟩ ⦇⌜ d4 ⌟⦈⟨ x ⟩ eq1 (Eq0NEHole eq2) with eq0-subst d3 d4 eq1 eq2 
  ... | eq3 = {!  !}
  eq0-subst (d3 ∘ d3') (d4 ∘ d4') eq1 (Eq0Ap eq2 eq3) with eq0-subst d3 d4 eq1 eq2 | eq0-subst d3' d4' eq1 eq3
  ... | eq4 | eq5 = Eq0Ap eq4 eq5
  eq0-subst (d3 < τ1 >) (d4 < τ2 >) eq1 (Eq0TAp eq2) with eq0-subst d3 d4 eq1 eq2
  ... | eq3 = Eq0TAp eq3
  eq0-subst (d3 ⟨ x ⇒ x₁ ⟩) (d4 ⟨ x ⇒ x₁ ⟩) eq1 (Eq0Cast eq2) with eq0-subst d3 d4 eq1 eq2 
  ... | eq3 = Eq0Cast eq3
  eq0-subst (d3 ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) (d4 ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) eq1 (Eq0FailedCast eq2) with eq0-subst d3 d4 eq1 eq2 
  ... | eq3 = Eq0FailedCast eq3

  eq0-typsubst : 
    ∀ {t τ1 τ2} →
    (d1 d2 : ihexp) →
    d1 =0 d2 →
    (Ihexp[ τ1 / t ] d1) =0 (Ihexp[ τ2 / t ] d2)
  eq0-typsubst .c .c Eq0Const = Eq0Const
  eq0-typsubst .(X _) .(X _) Eq0Var = Eq0Var
  eq0-typsubst .(⦇-⦈⟨ _ ⟩) .(⦇-⦈⟨ _ ⟩) Eq0EHole = {!   !}
  eq0-typsubst (·λ _ [ _ ] d1) (·λ _ [ _ ] d2) (Eq0Lam eq) = Eq0Lam (eq0-typsubst d1 d2 eq)
  eq0-typsubst {t = t} (·Λ t' d1) (·Λ t' d2) (Eq0TLam eq) with natEQ t t' 
  ... | Inl refl = Eq0TLam eq
  ... | Inr x = Eq0TLam (eq0-typsubst d1 d2 eq)
  eq0-typsubst .(⦇⌜ _ ⌟⦈⟨ _ ⟩) .(⦇⌜ _ ⌟⦈⟨ _ ⟩) (Eq0NEHole eq) = {!   !}
  eq0-typsubst (d1 ∘ d2) (d3 ∘ d4) (Eq0Ap eq eq₁) = Eq0Ap (eq0-typsubst d1 d3 eq) (eq0-typsubst d2 d4 eq₁)
  eq0-typsubst (d1 < _ >) (d2 < _ >) (Eq0TAp eq) = Eq0TAp (eq0-typsubst d1 d2 eq)
  eq0-typsubst (d1 ⟨ _ ⇒ _ ⟩) (d2 ⟨ _ ⇒ _ ⟩) (Eq0Cast eq) = {!   !}
  eq0-typsubst (d1 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) (d2 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) (Eq0FailedCast eq) = {!   !}
  
  eq0-ctxin : 
    ∀ {d1 d2 d1' ε1} →
    d1 =0 d2 →
    d1 == ε1 ⟦ d1' ⟧ →
    Σ[ d2' ∈ ihexp ] Σ[ ε2 ∈ ectx ] ((d2 == ε2 ⟦ d2' ⟧) × (d1' =0 d2') × (ε1 =0ε ε2))
  eq0-ctxin eq FHOuter = _ , ⊙ , FHOuter , eq , Eq0Dot
  eq0-ctxin (Eq0NEHole eq) (FHNEHole ctxin) with eq0-ctxin eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHNEHole eq1 , eq2 , Eq0NEHole eq3
  eq0-ctxin (Eq0Ap eq eq₁) (FHAp1 ctxin) with eq0-ctxin eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHAp1 eq1 , eq2 , Eq0Ap1 eq3 eq₁
  eq0-ctxin (Eq0Ap eq eq₁) (FHAp2 ctxin) with eq0-ctxin eq₁ ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHAp2 eq1 , eq2 , Eq0Ap2 eq3 eq
  eq0-ctxin (Eq0TAp eq) (FHTAp ctxin) with eq0-ctxin eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 =  _ , _ , FHTAp eq1 , eq2 , Eq0TAp eq3
  eq0-ctxin (Eq0Cast eq) (FHCast ctxin) with eq0-ctxin eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHCast eq1 , eq2 , Eq0Cast eq3
  eq0-ctxin (Eq0FailedCast eq) (FHFailedCast ctxin) with eq0-ctxin eq ctxin
  ... | d2' , ε2 , eq1 , eq2 , eq3 =  _ , _ , FHFailedCast eq1 , eq2 , Eq0FailedCast eq3

  eq0-ctxout : 
    ∀ {d1 d1' d2' ε1 ε2} →
    d1' =0 d2' →
    ε1 =0ε ε2 →
    d1 == ε1 ⟦ d1' ⟧ →
    Σ[ d2 ∈ ihexp ] ((d2 == ε2 ⟦ d2' ⟧) × (d1 =0 d2))
  eq0-ctxout eq1 Eq0Dot FHOuter = _ , FHOuter , eq1
  eq0-ctxout eq1 (Eq0Ap1 eq2 x) (FHAp1 eq3) with eq0-ctxout eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHAp1 eq4 , Eq0Ap eq5 x
  eq0-ctxout eq1 (Eq0Ap2 eq2 x) (FHAp2 eq3) with eq0-ctxout eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHAp2 eq4 , Eq0Ap x eq5
  eq0-ctxout eq1 (Eq0TAp eq2) (FHTAp eq3) with eq0-ctxout eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHTAp eq4 , Eq0TAp eq5
  eq0-ctxout eq1 (Eq0NEHole eq2) (FHNEHole eq3) with eq0-ctxout eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHNEHole eq4 , Eq0NEHole eq5
  eq0-ctxout eq1 (Eq0Cast eq2) (FHCast eq3) with eq0-ctxout eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHCast eq4 , Eq0Cast eq5
  eq0-ctxout eq1 (Eq0FailedCast eq2) (FHFailedCast eq3) with eq0-ctxout eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHFailedCast eq4 , Eq0FailedCast eq5

  eq0-instep : 
    ∀ {d1 d2 d1'} →
    d1 =0 d2 →
    d1 →> d1' →
    Σ[ d2' ∈ ihexp ] ((d2 →> d2') × (d1' =0 d2'))
  eq0-instep {d1 = (·λ x [ τ1 ] d5) ∘ d2} {d2 = (·λ x [ τ ] d3) ∘ d4} (Eq0Ap (Eq0Lam eq) eq₁) ITLam = ([ d4 / x ] d3) , ITLam , eq0-subst d5 d3 eq₁ eq
  eq0-instep {d1 = (d5 ⟨ τ1 ==> τ2 ⇒ τ1' ==> τ2' ⟩) ∘ d6} {d2 = (d3 ⟨ τ1 ==> τ2 ⇒ τ1' ==> τ2' ⟩) ∘ d4} (Eq0Ap (Eq0Cast eq) eq₁) ITApCast = ((d3 ∘ (d4 ⟨ τ1' ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ2' ⟩) , ITApCast , Eq0Cast (Eq0Ap eq (Eq0Cast eq₁))
  eq0-instep {d1 = ·Λ t d1 < τ1 >} {d2 = ·Λ .t d2 < τ2 >} (Eq0TAp (Eq0TLam eq)) ITTLam = (Ihexp[ τ2 / t ] d2) , ITTLam , {!   !}
  eq0-instep {d1 = ((d1 ⟨ ·∀ t τ ⇒ ·∀ t' τ' ⟩) < τ1 >)} {d2 = ((d2 ⟨ ·∀ t τ ⇒ ·∀ t' τ' ⟩) < τ2 >)} (Eq0TAp (Eq0Cast eq)) ITTApCast = ((d2 < τ2 >) ⟨ Typ[ τ2 / t ] τ ⇒ Typ[ τ2 / t' ] τ' ⟩) , ITTApCast , {!   !}
  eq0-instep {d2 = d2 ⟨ τ1 ⇒ τ2 ⟩} (Eq0Cast eq) (ITCastID x) = d2 , ITCastID x , eq 
  eq0-instep {d2 = ((d2 ⟨ _ ⇒ ⦇-⦈ ⟩) ⟨ ⦇-⦈ ⇒ _ ⟩)} (Eq0Cast (Eq0Cast eq)) (ITCastSucceed x x₁ x₂) = d2 , ITCastSucceed x x₁ x₂ , eq
  eq0-instep {d2 = ((d2 ⟨ τ1 ⇒ ⦇-⦈ ⟩) ⟨ ⦇-⦈ ⇒ τ2 ⟩)} (Eq0Cast (Eq0Cast eq)) (ITCastFail x x₁ x₂) = d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ , ITCastFail x x₁ x₂ , Eq0FailedCast eq
  eq0-instep {d2 = (d2 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} (Eq0Cast eq) (ITGround {τ' = τ'} x) = ((d2 ⟨ τ1 ⇒ τ' ⟩) ⟨ τ' ⇒ ⦇-⦈ ⟩) , ITGround x , Eq0Cast (Eq0Cast eq)
  eq0-instep {d2 = (d2 ⟨ ⦇-⦈ ⇒ τ1 ⟩)} (Eq0Cast eq) (ITExpand {τ' = τ'} x) = ((d2 ⟨ ⦇-⦈ ⇒ τ' ⟩) ⟨ τ' ⇒ τ1 ⟩) , ITExpand x , Eq0Cast (Eq0Cast eq)

  eq0-step : 
    ∀ {d1 d2 d1'} →
    d1 =0 d2 →
    d1 ↦ d1' →
    Σ[ d2' ∈ ihexp ] ((d2 ↦ d2') × (d1' =0 d2'))
  eq0-step eq (Step ctx1 step1 ctx2) 
    with eq0-ctxin eq ctx1
  ... | ( d3 , ε' , ctx3 , eq2 , eq3 ) 
    with eq0-instep eq2 step1
  ... | ( d4 , step2 , eq4 ) 
    with eq0-ctxout eq4 eq3 ctx2 
  ... | d5 , eq5 , eq6 =  d5 , Step ctx3 step2 eq5 , eq6 

  parametricity11 : 
    ∀ {e Θ Γ τ d1 Δ d2 v1 } →
    e ecomplete →
    Θ , Γ ⊢ e ⇒ τ ~> d1 ⊣ Δ →
    d1 =0 d2 →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ] ((d2 ↦* v2) × (v2 boxedval) × (v1 =0 v2))
  parametricity11 complete wt eq MSRefl bv = _ , MSRefl , eq0-boxedval eq bv , eq 
  parametricity11 complete wt eq (MSStep step steps) bv 
    with eq0-step eq step 
  ... | ( d2' , step2 , eq2 )
    with (parametricity11 complete {!   !} eq2 steps bv)
  ... | ( v2 , steps2 , bv2 , eq3 ) = v2 , MSStep step2 steps2  , bv2 , eq3
      

  -- Recycling bin:

  -- fill-hole : (d : ihexp) (ε : ectx) → Σ[ d' ∈ ihexp ] (d' == ε ⟦ d ⟧)
  -- fill-hole d ⊙ = d , FHOuter
  -- fill-hole d (ε ∘₁ x) with fill-hole d ε 
  -- ... | d' , fill = d' ∘ x , FHAp1 fill
  -- fill-hole d (x ∘₂ ε) with fill-hole d ε 
  -- ... | d' , fill = x ∘ d' , FHAp2 fill
  -- fill-hole d (ε < x >) with fill-hole d ε 
  -- ... | d' , fill = d' < x > , FHTAp fill
  -- fill-hole d ⦇⌜ ε ⌟⦈⟨ x ⟩ with fill-hole d ε 
  -- ... | d' , fill = ⦇⌜ d' ⌟⦈⟨ x ⟩ , FHNEHole fill
  -- fill-hole d (ε ⟨ x ⇒ x₁ ⟩) with fill-hole d ε 
  -- ... | d' , fill = d' ⟨ x ⇒ x₁ ⟩ , FHCast fill
  -- fill-hole d (ε ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) with fill-hole d ε 
  -- ... | d' , fill = d' ⟨ x ⇒⦇-⦈⇏ x₁ ⟩ , FHFailedCast fill

  -- fill-hole-function : (d : ihexp) (ε : ectx) → ihexp
  -- fill-hole-function d ε with fill-hole d ε
  -- ... | d' , _ = d'
