open import Nat
open import Prelude
open import core
open alpha
open import lemmas-alpha
open import lemmas-typ-subst
open import lemmas-well-formed
open import lemmas-consistency
open import complete-preservation
open import typed-elaboration
open import complete-elaboration
open import preservation

open import contexts

module parametricity where

  data _=0_ : (d1 d2 : ihexp) → Set where 
    Eq0Const : c =0 c
    Eq0Var : ∀{x} → (X x) =0 (X x) 
    Eq0EHole : ∀{u θ θ' σ σ'} → ⦇-⦈⟨ u , θ , σ ⟩ =0 ⦇-⦈⟨ u , θ' , σ' ⟩
    -- TODO: We ignore the subsitution stuff, but this should be addressible with something like recursiing into sigma while allowing variation in theta
    Eq0Lam : ∀{x d1 d2 τ1 τ2} → d1 =0 d2 → (·λ x [ τ1 ] d1) =0 (·λ x [ τ2 ] d2)
    Eq0TLam : ∀{t d1 d2} → d1 =0 d2 → (·Λ t d1) =0 (·Λ t d2)
    Eq0NEHole : ∀{u d1 d2 θ θ' σ σ'} → d1 =0 d2 →  (⦇⌜ d1 ⌟⦈⟨ u , θ , σ ⟩) =0 (⦇⌜ d2 ⌟⦈⟨ u , θ' , σ' ⟩)
    Eq0Ap :  ∀{d1 d2 d3 d4} → d1 =0 d3 →  d2 =0 d4 →  (d1 ∘ d2) =0 (d3 ∘ d4)
    Eq0TAp : ∀{d1 d2 τ1 τ2} → d1 =0 d2 → (d1 < τ1 >) =0 (d2 < τ2 >)
    Eq0Cast : ∀{d1 d2 τ1 τ2 τ3 τ4} → d1 =0 d2 → (d1 ⟨ τ1 ⇒ τ2 ⟩) =0 (d2 ⟨ τ3 ⇒ τ4 ⟩)
    Eq0FailedCast : ∀{d1 d2 τ1 τ2 τ3 τ4} → d1 =0 d2 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0 (d2 ⟨ τ3 ⇒⦇-⦈⇏ τ4 ⟩)

  data _=0'_ : (d1 d2 : ihexp) → Set where 
    Eq0Const : c =0' c
    Eq0Var : ∀{x} → (X x) =0' (X x) 
    Eq0EHole : ∀{u θ θ' σ σ'} → ⦇-⦈⟨ u , θ , σ ⟩ =0' ⦇-⦈⟨ u , θ' , σ' ⟩
    Eq0Lam : ∀{x d1 d2 τ1 τ2} → d1 =0' d2 → (·λ x [ τ1 ] d1) =0' (·λ x [ τ2 ] d2)
    Eq0TLam : ∀{t d1 d2} → d1 =0' d2 → (·Λ t d1) =0' (·Λ t d2)
    Eq0NEHole : ∀{u d1 d2 θ θ' σ σ'} → d1 =0' d2 →  (⦇⌜ d1 ⌟⦈⟨ u , θ , σ ⟩) =0' (⦇⌜ d2 ⌟⦈⟨ u , θ' , σ' ⟩)
    Eq0Ap :  ∀{d1 d2 d3 d4} → d1 =0' d3 →  d2 =0' d4 →  (d1 ∘ d2) =0' (d3 ∘ d4)
    Eq0TAp : ∀{d1 d2 τ1 τ2} → d1 =0' d2 → (d1 < τ1 >) =0' (d2 < τ2 >)
    Eq0Cast : ∀{d1 d2 τ1 τ1' τ2 τ2'} → d1 =0' d2 → τ1 =α τ1' → τ2 =α τ2' → (d1 ⟨ τ1 ⇒ τ1' ⟩) =0' (d2 ⟨ τ2 ⇒ τ2' ⟩)
    Eq0FailedCast : ∀{d1 d2 τ1 τ2} → d1 =0' d2 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0' (d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  data _=0e_ : (e1 e2 : hexp) → Set where
    Eq0Const : c =0e c
    Eq0Var : ∀{x} → (X x) =0e (X x) 
    Eq0Asc : ∀{e1 e2 τ1 τ2} → e1 =0e e2 → (e1 ·: τ1) =0e (e2 ·: τ2)
    Eq0EHole : ∀{u} → ⦇-⦈[ u ] =0e ⦇-⦈[ u ]
    Eq0ULam : ∀{x e1 e2} → e1 =0e e2 → (·λ x e1) =0e (·λ x e2)
    Eq0Lam : ∀{x e1 e2 τ1 τ2} → e1 =0e e2 → (·λ x [ τ1 ] e1) =0e (·λ x [ τ2 ] e2)
    Eq0TLam : ∀{t e1 e2} → e1 =0e e2 → (·Λ t e1) =0e (·Λ t e2)
    Eq0NEHole : ∀{u e1 e2} → e1 =0e e2 →  (⦇⌜ e1 ⌟⦈[ u ]) =0e (⦇⌜ e2 ⌟⦈[ u ])
    Eq0Ap :  ∀{e1 e2 e3 e4} → e1 =0e e3 →  e2 =0e e4 →  (e1 ∘ e2) =0e (e3 ∘ e4)
    Eq0TAp : ∀{e1 e2 τ1 τ2} → e1 =0e e2 → (e1 < τ1 >) =0e (e2 < τ2 >)

  data _=0ε'_ : (ε1 ε2 : ectx) → Set where 
    Eq0Dot : ⊙ =0ε' ⊙
    Eq0Ap1 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε' ε2) → (d1 =0' d2) → (ε1 ∘₁ d1) =0ε' (ε2 ∘₁ d2)
    Eq0Ap2 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε' ε2) → (d1 =0' d2) → (d1 ∘₂ ε1) =0ε' (d2 ∘₂ ε2)
    Eq0TAp : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε' ε2) → (ε1 < τ1 >) =0ε' (ε2 < τ2 >)
    Eq0NEHole : ∀{ε1 ε2 u θ θ' σ σ'} → (ε1 =0ε' ε2) → (⦇⌜ ε1 ⌟⦈⟨ u , θ , σ ⟩) =0ε' (⦇⌜ ε2 ⌟⦈⟨ u , θ' , σ' ⟩)
    Eq0Cast : ∀{ε1 ε2 τ1 τ1' τ2 τ2'} → (ε1 =0ε' ε2) → τ1 =α τ1' → τ2 =α τ2' → (ε1 ⟨ τ1 ⇒ τ1' ⟩) =0ε' (ε2 ⟨ τ2 ⇒ τ2' ⟩)
    Eq0FailedCast : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε' ε2) → (ε1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0ε' (ε2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

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

  eq0-sym : ∀{d d' : ihexp} → d =0 d' → d' =0 d
  eq0-sym Eq0Const = Eq0Const
  eq0-sym Eq0Var = Eq0Var
  eq0-sym Eq0EHole = Eq0EHole
  eq0-sym (Eq0Lam eq0) = Eq0Lam (eq0-sym eq0)
  eq0-sym (Eq0TLam eq0) = Eq0TLam (eq0-sym eq0)
  eq0-sym (Eq0NEHole eq0) = Eq0NEHole (eq0-sym eq0)
  eq0-sym (Eq0Ap eq0 eq1) = Eq0Ap (eq0-sym eq0) (eq0-sym eq1)
  eq0-sym (Eq0TAp eq0) = Eq0TAp (eq0-sym eq0)
  eq0-sym (Eq0Cast eq0) = Eq0Cast (eq0-sym eq0)
  eq0-sym (Eq0FailedCast eq0) = Eq0FailedCast (eq0-sym eq0)


  eq0e-sym : ∀{e e' : hexp} → e =0e e' → e' =0e e
  eq0e-sym Eq0Const = Eq0Const
  eq0e-sym Eq0Var = Eq0Var
  eq0e-sym (Eq0Asc eq0) = Eq0Asc (eq0e-sym eq0)
  eq0e-sym Eq0EHole = Eq0EHole
  eq0e-sym (Eq0ULam eq0) = Eq0ULam (eq0e-sym eq0)
  eq0e-sym (Eq0Lam eq0) = Eq0Lam (eq0e-sym eq0)
  eq0e-sym (Eq0TLam eq0) = Eq0TLam (eq0e-sym eq0)
  eq0e-sym (Eq0NEHole eq0) = Eq0NEHole (eq0e-sym eq0)
  eq0e-sym (Eq0Ap eq0 eq1) = Eq0Ap (eq0e-sym eq0) (eq0e-sym eq1)
  eq0e-sym (Eq0TAp eq0) = Eq0TAp (eq0e-sym eq0)

{-
  eq0ε-refl : ∀{ε : ectx} → ε =0ε' ε
  eq0ε-refl {ε = ⊙} = Eq0Dot
  eq0ε-refl {ε = ε ∘₁ x} = Eq0Ap1 eq0ε-refl eq0-refl
  eq0ε-refl {ε = x ∘₂ ε} = Eq0Ap2 eq0ε-refl eq0-refl
  eq0ε-refl {ε = ε < x >} = Eq0TAp eq0ε-refl
  eq0ε-refl {ε = ⦇⌜ ε ⌟⦈⟨ x ⟩} = Eq0NEHole eq0ε-refl
  eq0ε-refl {ε = ε ⟨ x ⇒ x₁ ⟩} = Eq0Cast eq0ε-refl
  eq0ε-refl {ε = ε ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} = Eq0FailedCast eq0ε-refl
-}

  eq0-boxedval' : 
    ∀ {d1 d2} →
    d1 =0' d2 →
    d1 boxedval →
    d2 boxedval
  eq0-boxedval' {d2 = d2} Eq0Const bv = bv
  eq0-boxedval' {d2 = d2} Eq0Var bv = bv
  eq0-boxedval' {d2 = d2} (Eq0Lam eq) bv = BVVal VLam
  eq0-boxedval' {d2 = d2} (Eq0TLam eq) bv = BVVal VTLam
  eq0-boxedval' (Eq0Cast eq alpha1 alpha2) (BVArrCast x bv) = abort (x alpha1)
  eq0-boxedval' (Eq0Cast eq alpha1 alpha2) (BVForallCast x bv) = abort (x alpha1) -- BVForallCast x (eq0-boxedval' eq bv)
  eq0-boxedval' (Eq0Cast eq () alpha2) (BVHoleCast GBase bv)
  eq0-boxedval' (Eq0Cast eq () alpha2) (BVHoleCast GArr bv)
  eq0-boxedval' (Eq0Cast eq () alpha2) (BVHoleCast GForall bv)
  eq0-boxedval' Eq0EHole (BVVal ())
  eq0-boxedval' (Eq0NEHole eq) (BVVal ())
  eq0-boxedval' (Eq0Ap eq eq₁) (BVVal ())
  eq0-boxedval' (Eq0TAp eq) (BVVal ())
  eq0-boxedval' (Eq0FailedCast x₁) (BVVal ())


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
  eq0-subst ⦇-⦈⟨ x ⟩ ⦇-⦈⟨ x' ⟩ eq1 Eq0EHole = Eq0EHole
  eq0-subst ⦇⌜ d3 ⌟⦈⟨ x ⟩ ⦇⌜ d4 ⌟⦈⟨ x' ⟩ eq1 (Eq0NEHole eq2) with eq0-subst d3 d4 eq1 eq2 
  ... | eq3 = Eq0NEHole (eq0-subst d3 d4 eq1 eq2)
  eq0-subst (d3 ∘ d3') (d4 ∘ d4') eq1 (Eq0Ap eq2 eq3) with eq0-subst d3 d4 eq1 eq2 | eq0-subst d3' d4' eq1 eq3
  ... | eq4 | eq5 = Eq0Ap eq4 eq5
  eq0-subst (d3 < τ1 >) (d4 < τ2 >) eq1 (Eq0TAp eq2) with eq0-subst d3 d4 eq1 eq2
  ... | eq3 = Eq0TAp eq3
  eq0-subst (d3 ⟨ x ⇒ x₁ ⟩) (d4 ⟨ x' ⇒ x₁' ⟩) eq1 (Eq0Cast eq2) with eq0-subst d3 d4 eq1 eq2 
  ... | eq3 = Eq0Cast eq3
  eq0-subst (d3 ⟨ x ⇒⦇-⦈⇏ x₁ ⟩) (d4 ⟨ x' ⇒⦇-⦈⇏ x₁' ⟩) eq1 (Eq0FailedCast eq2) with eq0-subst d3 d4 eq1 eq2 
  ... | eq3 = Eq0FailedCast eq3


  eq0-typsubst : 
    ∀ {t τ1 τ2} →
    (d1 d2 : ihexp) →
    d1 =0 d2 →
    (Ihexp[ τ1 / t ] d1) =0 (Ihexp[ τ2 / t ] d2)
  eq0-typsubst .c .c Eq0Const = Eq0Const
  eq0-typsubst .(X _) .(X _) Eq0Var = Eq0Var
  eq0-typsubst .(⦇-⦈⟨ _ ⟩) .(⦇-⦈⟨ _ ⟩) Eq0EHole = Eq0EHole
  eq0-typsubst (·λ _ [ _ ] d1) (·λ _ [ _ ] d2) (Eq0Lam eq) = Eq0Lam (eq0-typsubst d1 d2 eq)
  eq0-typsubst {t = t} (·Λ t' d1) (·Λ t' d2) (Eq0TLam eq) with natEQ t t' 
  ... | Inl refl = Eq0TLam eq
  ... | Inr x = Eq0TLam (eq0-typsubst d1 d2 eq)
  eq0-typsubst (⦇⌜ d1 ⌟⦈⟨ _ ⟩) (⦇⌜ d2 ⌟⦈⟨ _ ⟩) (Eq0NEHole eq) = Eq0NEHole (eq0-typsubst d1 d2 eq)
  eq0-typsubst (d1 ∘ d2) (d3 ∘ d4) (Eq0Ap eq eq₁) = Eq0Ap (eq0-typsubst d1 d3 eq) (eq0-typsubst d2 d4 eq₁)
  eq0-typsubst (d1 < _ >) (d2 < _ >) (Eq0TAp eq) = Eq0TAp (eq0-typsubst d1 d2 eq)
  eq0-typsubst (d1 ⟨ _ ⇒ _ ⟩) (d2 ⟨ _ ⇒ _ ⟩) (Eq0Cast eq) = Eq0Cast (eq0-typsubst d1 d2 eq)
  eq0-typsubst (d1 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) (d2 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) (Eq0FailedCast eq) = Eq0FailedCast (eq0-typsubst d1 d2 eq)

  eq0-subst' : 
    ∀ {x d1 d2} →
    (d3 d4 : ihexp) →
    d1 =0' d2 →
    d3 =0' d4 →
    ([ d1 / x ] d3) =0' ([ d2 / x ] d4)
  eq0-subst' .c .c eq0 Eq0Const = Eq0Const
  eq0-subst' {x = x} (X y) .(X y) eq0 Eq0Var with natEQ y x
  ... | Inl refl = eq0
  ... | Inr neq rewrite natEQneq neq = Eq0Var
  eq0-subst' (⦇-⦈⟨ u3 ⟩) (⦇-⦈⟨ u5 ⟩) eq0 Eq0EHole = Eq0EHole
  eq0-subst' {x} (·λ x3 [ t3 ] d3) (·λ x4 [ t4 ] d4) eq0 (Eq0Lam eq0') with natEQ x3 x 
  ... | Inl refl = Eq0Lam eq0'
  ... | Inr neq = Eq0Lam (eq0-subst' d3 d4 eq0 eq0')
  eq0-subst' (·Λ t3 d3) (·Λ t4 d4) eq0 (Eq0TLam eq0') = Eq0TLam (eq0-subst' d3 d4 eq0 eq0')
  eq0-subst' (⦇⌜ d3 ⌟⦈⟨ u3 ⟩) (⦇⌜ d4 ⌟⦈⟨ u4 ⟩) eq0 (Eq0NEHole eq0') = Eq0NEHole (eq0-subst' d3 d4 eq0 eq0') -- Eq0EHole
  eq0-subst' (d3 ∘ d3') (d4 ∘ d4') eq0 (Eq0Ap eq0' eq0'') = Eq0Ap (eq0-subst' d3 d4 eq0 eq0') (eq0-subst' d3' d4' eq0 eq0'')
  eq0-subst' (d3 < t3 >) (d4 < t4 >) eq0 (Eq0TAp eq0') = Eq0TAp (eq0-subst' d3 d4 eq0 eq0')
  eq0-subst' (d3 ⟨ t3 ⇒ t3' ⟩) (d4 ⟨ t4 ⇒ t4' ⟩) eq0 (Eq0Cast eq0' x x₁) = Eq0Cast (eq0-subst' d3 d4 eq0 eq0') x x₁
  eq0-subst' (d3 ⟨ t3 ⇒⦇-⦈⇏ t3' ⟩) (d4 ⟨ t4 ⇒⦇-⦈⇏ t4' ⟩) eq0 (Eq0FailedCast eq0') = Eq0FailedCast (eq0-subst' d3 d4 eq0 eq0')

  eq0-typsubst' : 
    ∀ {t τ1 τ2} →
    (d1 d2 : ihexp) →
    d1 dcompleteid →
    ∅ ⊢ τ1 wf → ∅ ⊢ τ2 wf →
    d1 =0' d2 →
    (Ihexp[ τ1 / t ] d1) =0' (Ihexp[ τ2 / t ] d2)
  eq0-typsubst' c .c compl _ _ Eq0Const = Eq0Const
  eq0-typsubst' (X x) .(X x) compl _ _ Eq0Var = Eq0Var
  eq0-typsubst' (·λ x [ x₁ ] d1) (·λ x [ _ ] d2) (DCLam compl _) wf1 wf2 (Eq0Lam eq0) = Eq0Lam (eq0-typsubst' d1 d2 compl wf1 wf2 eq0)
  eq0-typsubst' {t = t} (·Λ x d1) (·Λ x d2) (DCTLam compl) wf1 wf2 (Eq0TLam eq0) with natEQ t x
  ...  | Inl refl = Eq0TLam eq0
  ...  | Inr neq = Eq0TLam (eq0-typsubst' d1 d2 compl wf1 wf2 eq0)
  eq0-typsubst' (d1 ∘ d2) (d3 ∘ d4) (DCAp compl compl₁) wf1 wf2 (Eq0Ap eq0 eq1) = Eq0Ap (eq0-typsubst' d1 d3 compl wf1 wf2 eq0) (eq0-typsubst' d2 d4 compl₁ wf1 wf2 eq1)
  eq0-typsubst' (d1 < x >) (d2 < x₁ >) (DCTAp x₂ compl) wf1 wf2 (Eq0TAp eq0) = Eq0TAp (eq0-typsubst' d1 d2 compl wf1 wf2 eq0)
  eq0-typsubst' (d1 ⟨ x ⇒ x' ⟩) (d2 ⟨ x₂ ⇒ x₂' ⟩) (DCCast compl t1compl t2compl alpha) wf1 wf2 (Eq0Cast eq0 alphal alphar) = Eq0Cast (eq0-typsubst' d1 d2 compl wf1 wf2 eq0) (alpha-sub wf1 (lemma-alpha-forall alphal)) (alpha-sub wf2 (lemma-alpha-forall alphar))

{-
  eq0'-eq0 :
    ∀{v v'} →
    v boxedval →
    v' boxedval →
    v =0' v' →
    v =0 v'
  eq0'-eq0 bv bv' Eq0Const = Eq0Const
  eq0'-eq0 bv bv' Eq0Var = Eq0Var
  eq0'-eq0 bv bv' Eq0EHole = Eq0EHole
  eq0'-eq0 (BVVal VLam) (BVVal VLam) (Eq0Lam eq0') = Eq0Lam (eq0'-eq0 {!   !} {!   !} eq0') 
  eq0'-eq0 bv bv' (Eq0TLam eq0') = {!   !}
  eq0'-eq0 bv bv' (Eq0NEHole eq0') = {!   !}
  eq0'-eq0 bv bv' (Eq0Ap eq0' eq0'') = {!   !}
  eq0'-eq0 bv bv' (Eq0TAp eq0') = {!   !}
  eq0'-eq0 (BVArrCast {τ1 = τ1} {τ2 = τ2} x bv) bv' (Eq0Cast eq0') = abort (x (alpha-refl (τ1 ==> τ2)))
  eq0'-eq0 (BVForallCast {t1 = t1} {τ1 = τ1} x bv) bv' (Eq0Cast eq0') = abort (x (alpha-refl (·∀ t1 τ1)))
  eq0'-eq0 bv bv' (Eq0FailedCast eq0') = {!   !}
-}

  eq0'-eq0 :
    ∀{d1 d2} →
    d1 =0' d2 →
    d1 =0 d2
  eq0'-eq0 Eq0Const = Eq0Const
  eq0'-eq0 Eq0Var = Eq0Var
  eq0'-eq0 Eq0EHole = Eq0EHole
  eq0'-eq0 (Eq0Lam eq0) = Eq0Lam (eq0'-eq0 eq0)
  eq0'-eq0 (Eq0TLam eq0) = Eq0TLam (eq0'-eq0 eq0)
  eq0'-eq0 (Eq0NEHole eq0) = Eq0NEHole (eq0'-eq0 eq0)
  eq0'-eq0 (Eq0Ap eq0 eq1) = Eq0Ap (eq0'-eq0 eq0) (eq0'-eq0 eq1)
  eq0'-eq0 (Eq0TAp eq0) = Eq0TAp (eq0'-eq0 eq0)
  eq0'-eq0 (Eq0Cast eq0 alphal alphar) = Eq0Cast (eq0'-eq0 eq0)
  eq0'-eq0 (Eq0FailedCast eq0) = Eq0FailedCast (eq0'-eq0 eq0)


  eq0-eq0' :
    ∀{d1 d2} →
    d1 dcompleteid →
    d2 dcompleteid →
    d1 =0 d2 →
    d1 =0' d2
  eq0-eq0' DCVar _ Eq0Var = Eq0Var
  eq0-eq0' DCConst _ Eq0Const = Eq0Const
  eq0-eq0' (DCLam complete x) (DCLam complete' x₁) (Eq0Lam eq0) = Eq0Lam (eq0-eq0' complete complete' eq0)
  eq0-eq0' (DCTLam complete) (DCTLam complete') (Eq0TLam eq0) = Eq0TLam (eq0-eq0' complete complete' eq0)
  eq0-eq0' (DCAp complete complete₁) (DCAp complete' complete'₁) (Eq0Ap eq0 eq1) = Eq0Ap (eq0-eq0' complete complete' eq0) (eq0-eq0' complete₁ complete'₁ eq1)
  eq0-eq0' (DCTAp x complete) (DCTAp x' complete') (Eq0TAp eq0) = Eq0TAp (eq0-eq0' complete complete' eq0)
  eq0-eq0' (DCCast complete t1compl t2compl alpha) (DCCast complete' t1compl' t2compl' alpha') (Eq0Cast eq0) = Eq0Cast (eq0-eq0' complete complete' eq0) alpha alpha'



{-
  eq0e-complete : ∀{e e'} →
    e ecomplete →
    e =0e e' →
    e' ecomplete
  eq0e-complete ECConst Eq0Const = ECConst
  eq0e-complete (ECAsc x ecompl) (Eq0Asc eq0) = ECAsc {!   !} (eq0e-complete ecompl eq0)
  eq0e-complete ECVar Eq0Var = ECVar
  eq0e-complete (ECLam1 ecompl) (Eq0ULam eq0) = {!   !}
  eq0e-complete (ECLam2 ecompl x) (Eq0Lam eq0) = {!   !}
  eq0e-complete (ECTLam ecompl) (Eq0TLam eq0) = {!   !}
  eq0e-complete (ECAp ecompl ecompl₁) (Eq0Ap eq0 eq1) = {!   !}
  eq0e-complete (ECTAp x ecompl) (Eq0TAp eq0) = {!   !}
-}


  mutual
    eq0-elab-syn : ∀{e e' Θ Γ Γ' d1 d2 τ τ' Δ Δ'} →
      e =0e e' →
      Θ , Γ ⊢ e ⇒ τ ~> d1 ⊣ Δ →
      Θ , Γ' ⊢ e' ⇒ τ' ~> d2 ⊣ Δ' →
      d1 =0 d2
    eq0-elab-syn Eq0Const ESConst ESConst = Eq0Const
    eq0-elab-syn Eq0Var (ESVar x) (ESVar x₁) = Eq0Var
    eq0-elab-syn (Eq0Asc eq0) (ESAsc x x₁) (ESAsc x₂ x₃) = Eq0Cast (eq0-elab-ana eq0 x₁ x₃)
    eq0-elab-syn Eq0EHole ESEHole ESEHole = Eq0EHole
    eq0-elab-syn (Eq0Lam eq0) (ESLam x x₁ elab1) (ESLam x₂ x₃ elab2) = Eq0Lam (eq0-elab-syn eq0 elab1 elab2)
    eq0-elab-syn (Eq0TLam eq0) (ESTLam elab1) (ESTLam elab2) = Eq0TLam (eq0-elab-syn eq0 elab1 elab2)
    eq0-elab-syn (Eq0NEHole eq0) (ESNEHole x elab1) (ESNEHole x' elab2) = Eq0NEHole (eq0-elab-syn eq0 elab1 elab2)
    eq0-elab-syn (Eq0Ap eq0 eq1) (ESAp x x₁ x₂ x₃ x₄ x₅) (ESAp x₆ x₇ x₈ x₉ x₁₀ x₁₁) = Eq0Ap (Eq0Cast (eq0-elab-ana eq0 x₄ x₁₀)) (Eq0Cast (eq0-elab-ana eq1 x₅ x₁₁))
    eq0-elab-syn (Eq0TAp eq0) (ESTAp x x₁ x₂ x₃ x₄) (ESTAp x₅ x₆ x₇ x₈ x₉) = Eq0TAp (Eq0Cast (eq0-elab-ana eq0 x₃ x₈))

    eq0-elab-ana : ∀{e e' Θ Γ Γ' d1 d2 τ1 τ1' τ2 τ2' Δ Δ'} →
      e =0e e' →
      Θ , Γ ⊢ e ⇐ τ1 ~> d1 :: τ1' ⊣ Δ →
      Θ , Γ' ⊢ e' ⇐ τ2 ~> d2 :: τ2' ⊣ Δ' →
      d1 =0 d2
    eq0-elab-ana eq0 (EASubsume x x₁ x₂ x₃) ana = eq0-elab-syn-ana eq0 x₂ ana
    eq0-elab-ana eq0 ana (EASubsume x x₁ x₂ x₃) = eq0-sym (eq0-elab-syn-ana (eq0e-sym eq0) x₂ ana)
    eq0-elab-ana Eq0EHole EAEHole EAEHole = Eq0EHole
    eq0-elab-ana (Eq0ULam eq0) (EALam x x₁ elab1) (EALam x₂ x₃ elab2) = Eq0Lam (eq0-elab-ana eq0 elab1 elab2)
    eq0-elab-ana (Eq0TLam eq0) (EATLam x x₁ x₂ elab1) (EATLam x₃ x₄ x₅ elab2) = Eq0TLam (eq0-elab-ana eq0 elab1 elab2)
    eq0-elab-ana (Eq0NEHole eq0) (EANEHole x x₁) (EANEHole x₂ x₃) = Eq0NEHole (eq0-elab-syn eq0 x₁ x₃)

    
    eq0-elab-syn-ana : ∀{e e' Θ Γ Γ' d1 d2 τ1 τ2 τ2' Δ Δ'} →
      e =0e e' →
      Θ , Γ ⊢ e ⇒ τ1 ~> d1 ⊣ Δ →
      Θ , Γ' ⊢ e' ⇐ τ2 ~> d2 :: τ2' ⊣ Δ' →
      d1 =0 d2
    eq0-elab-syn-ana eq0 syn (EASubsume x x₁ x₂ x₃) = eq0-elab-syn eq0 syn x₂
    eq0-elab-syn-ana Eq0EHole ESEHole EAEHole = Eq0EHole
    eq0-elab-syn-ana (Eq0ULam eq0) () ana
    eq0-elab-syn-ana (Eq0TLam eq0) (ESTLam syn) (EATLam x x₁ x₂ ana) = Eq0TLam (eq0-elab-syn-ana eq0 syn ana)
    eq0-elab-syn-ana (Eq0NEHole eq0) (ESNEHole x syn) (EANEHole x₁ x₂) = Eq0NEHole (eq0-elab-syn eq0 syn x₂)

  consist-complete-alpha : ∀{τ τ' ΓL ΓR} →
    τ tcomplete →
    τ' tcomplete →
    ΓL , ΓR ⊢ τ ~ τ' →
    ΓL , ΓR ⊢ τ =α τ'
  consist-complete-alpha TCBase TCBase ConsistBase = AlphaBase
  consist-complete-alpha TCVar TCVar (ConsistVarFree x x₁) = AlphaVarFree x x₁
  consist-complete-alpha TCVar TCVar (ConsistVarBound x x₁) = AlphaVarBound x x₁
  consist-complete-alpha (TCArr tc1 tc2) (TCArr tc3 tc4) (ConsistArr consis consis₁) = AlphaArr (consist-complete-alpha tc1 tc3 consis) (consist-complete-alpha tc2 tc4 consis₁)
  consist-complete-alpha (TCForall tc1) (TCForall tc2) (ConsistForall consis) = AlphaForall (consist-complete-alpha tc1 tc2 consis)

  empty-ctx-gcomplete : ∅ gcomplete
  empty-ctx-gcomplete x τ ()
  
  compl-wt-complid : ∀{d Θ Γ Δ τ} →
    d dcomplete →
    Δ , Θ , Γ ⊢ d :: τ →
    d dcompleteid
  compl-wt-complid DCVar (TAVar x) = DCVar
  compl-wt-complid DCConst TAConst = DCConst
  compl-wt-complid (DCLam compl x) (TALam x₁ x₂ wt) = DCLam (compl-wt-complid compl wt) x
  compl-wt-complid (DCTLam compl) (TATLam x wt) = DCTLam (compl-wt-complid compl wt)
  compl-wt-complid (DCAp compl compl₁) (TAAp wt wt₁ x) = DCAp (compl-wt-complid compl wt) (compl-wt-complid compl₁ wt₁)
  compl-wt-complid (DCTAp x compl) (TATAp x₁ wt x₂) = DCTAp x (compl-wt-complid compl wt)
  compl-wt-complid (DCCast compl x x₁) (TACast wt x₂ x₃ x₄) = DCCast (compl-wt-complid compl wt) x x₁ (consist-complete-alpha x x₁ x₃)

  complid-compl : ∀{d} →
    d dcompleteid →
    d dcomplete
  complid-compl DCVar = DCVar
  complid-compl DCConst = DCConst
  complid-compl (DCLam compl x) = DCLam (complid-compl compl) x
  complid-compl (DCTLam compl) = DCTLam (complid-compl compl)
  complid-compl (DCAp compl compl₁) = DCAp (complid-compl compl) (complid-compl compl₁)
  complid-compl (DCTAp x compl) = DCTAp x (complid-compl compl)
  complid-compl (DCCast compl x x₁ alpha) = DCCast (complid-compl compl) x x₁

  dcompleteid-elab : ∀{e τ Δ d} →
            e ecomplete →
            ∅ , ∅ ⊢ e ⇒ τ ~> d ⊣ Δ →
            d dcompleteid × Δ == ∅
  dcompleteid-elab ec elab with complete-elaboration-synth empty-ctx-gcomplete ec elab | typed-elaboration-synth wf-empty-tctx elab
  ... | (dc , tc , dempty) | wt = compl-wt-complid dc wt , dempty

  
  eq0-ctxin' : 
    ∀ {d1 d2 d1' ε1} →
    d1 =0' d2 →
    d1 == ε1 ⟦ d1' ⟧ →
    Σ[ d2' ∈ ihexp ] Σ[ ε2 ∈ ectx ] ((d2 == ε2 ⟦ d2' ⟧) × (d1' =0' d2') × (ε1 =0ε' ε2))
  eq0-ctxin' eq FHOuter = _ , ⊙ , FHOuter , eq , Eq0Dot
  eq0-ctxin' (Eq0NEHole eq) (FHNEHole ctxin) with eq0-ctxin' eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHNEHole eq1 , eq2 , Eq0NEHole eq3
  eq0-ctxin' (Eq0Ap eq eq₁) (FHAp1 ctxin) with eq0-ctxin' eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHAp1 eq1 , eq2 , Eq0Ap1 eq3 eq₁
  eq0-ctxin' (Eq0Ap eq eq₁) (FHAp2 ctxin) with eq0-ctxin' eq₁ ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHAp2 eq1 , eq2 , Eq0Ap2 eq3 eq
  eq0-ctxin' (Eq0TAp eq) (FHTAp ctxin) with eq0-ctxin' eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 =  _ , _ , FHTAp eq1 , eq2 , Eq0TAp eq3
  eq0-ctxin' (Eq0Cast eq alpha1 alpha2) (FHCast ctxin) with eq0-ctxin' eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHCast eq1 , eq2 , Eq0Cast eq3 alpha1 alpha2
  eq0-ctxin' (Eq0FailedCast eq) (FHFailedCast ctxin) with eq0-ctxin' eq ctxin
  ... | d2' , ε2 , eq1 , eq2 , eq3 =  _ , _ , FHFailedCast eq1 , eq2 , Eq0FailedCast eq3

  eq0-ctxout' : 
    ∀ {d1 d1' d2' ε1 ε2} →
    d1' =0' d2' →
    ε1 =0ε' ε2 →
    d1 == ε1 ⟦ d1' ⟧ →
    Σ[ d2 ∈ ihexp ] ((d2 == ε2 ⟦ d2' ⟧) × (d1 =0' d2))
  eq0-ctxout' eq1 Eq0Dot FHOuter = _ , FHOuter , eq1
  eq0-ctxout' eq1 (Eq0Ap1 eq2 x) (FHAp1 eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHAp1 eq4 , Eq0Ap eq5 x
  eq0-ctxout' eq1 (Eq0Ap2 eq2 x) (FHAp2 eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHAp2 eq4 , Eq0Ap x eq5
  eq0-ctxout' eq1 (Eq0TAp eq2) (FHTAp eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHTAp eq4 , Eq0TAp eq5
  eq0-ctxout' eq1 (Eq0NEHole eq2) (FHNEHole eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHNEHole eq4 , Eq0NEHole eq5
  eq0-ctxout' eq1 (Eq0Cast eq2 alpha1 alpha2) (FHCast eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHCast eq4 , Eq0Cast eq5 alpha1 alpha2
  eq0-ctxout' eq1 (Eq0FailedCast eq2) (FHFailedCast eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHFailedCast eq4 , Eq0FailedCast eq5


-- Might not be able to show that this hypothesis holds stepwise. Because the IHTyp doesn't work stepwise due to casts. But it does preserve identity casts which should eventually get evaluated away.
-- Make a new =0 judgment that allows for variation on identity casts, then show that after full evaluation, we don't have those anymore?
{-
  eq0-instep : 
    ∀ {d1 d2 d1'} →
    d1 =0 d2 →
    d1 →> d1' →
    Σ[ d2' ∈ ihexp ] ((d2 →> d2') × (d1' =0 d2'))
  eq0-instep {d1 = (·λ x [ τ1 ] d5) ∘ d2} {d2 = (·λ x [ τ ] d3) ∘ d4} (Eq0Ap (Eq0Lam eq) eq₁) ITLam = ([ d4 / x ] d3) , ITLam , eq0-subst d5 d3 eq₁ eq
  eq0-instep {d1 = (d5 ⟨ τ1 ==> τ2 ⇒ τ1' ==> τ2' ⟩) ∘ d6} {d2 = (d3 ⟨ τ1 ==> τ2 ⇒ τ1' ==> τ2' ⟩) ∘ d4} (Eq0Ap (Eq0Cast eq) eq₁) ITApCast = ((d3 ∘ (d4 ⟨ τ1' ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ2' ⟩) , ITApCast , Eq0Cast (Eq0Ap eq (Eq0Cast eq₁))
  eq0-instep {d1 = ·Λ t d1 < τ1 >} {d2 = ·Λ .t d2 < τ2 >} (Eq0TAp (Eq0TLam eq)) ITTLam = (Ihexp[ τ2 / t ] d2) , ITTLam , eq0-typsubst d1 d2 {!   !} eq
  eq0-instep {d1 = ((d1 ⟨ ·∀ t τ ⇒ ·∀ t' τ' ⟩) < τ1 >)} {d2 = ((d2 ⟨ ·∀ t τ ⇒ ·∀ t' τ' ⟩) < τ2 >)} (Eq0TAp (Eq0Cast eq)) ITTApCast = ((d2 < τ2 >) ⟨ Typ[ τ2 / t ] τ ⇒ Typ[ τ2 / t' ] τ' ⟩) , ITTApCast , {!   !}
  eq0-instep {d2 = d2 ⟨ τ1 ⇒ τ2 ⟩} (Eq0Cast eq) (ITCastID x) = d2 , ITCastID x , eq 
  eq0-instep {d2 = ((d2 ⟨ _ ⇒ ⦇-⦈ ⟩) ⟨ ⦇-⦈ ⇒ _ ⟩)} (Eq0Cast (Eq0Cast eq)) (ITCastSucceed x x₁ x₂) = d2 , ITCastSucceed x x₁ x₂ , eq
  eq0-instep {d2 = ((d2 ⟨ τ1 ⇒ ⦇-⦈ ⟩) ⟨ ⦇-⦈ ⇒ τ2 ⟩)} (Eq0Cast (Eq0Cast eq)) (ITCastFail x x₁ x₂) = d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ , ITCastFail x x₁ x₂ , Eq0FailedCast eq
  eq0-instep {d2 = (d2 ⟨ τ1 ⇒ ⦇-⦈ ⟩)} (Eq0Cast eq) (ITGround {τ' = τ'} x) = ((d2 ⟨ τ1 ⇒ τ' ⟩) ⟨ τ' ⇒ ⦇-⦈ ⟩) , ITGround x , Eq0Cast (Eq0Cast eq)
  eq0-instep {d2 = (d2 ⟨ ⦇-⦈ ⇒ τ1 ⟩)} (Eq0Cast eq) (ITExpand {τ' = τ'} x) = ((d2 ⟨ ⦇-⦈ ⇒ τ' ⟩) ⟨ τ' ⇒ τ1 ⟩) , ITExpand x , Eq0Cast (Eq0Cast eq)
-}

  eq0-instep' : 
    ∀ {d1 d2 d1' τ τ'} →
    d1 =0' d2 →
    d1 →> d1' →
    d1 dcompleteid →
    ∅ , ∅ , ∅ ⊢ d1 :: τ →
    ∅ , ∅ , ∅ ⊢ d2 :: τ' →
    Σ[ d2' ∈ ihexp ] ((d2 →> d2') × (d1' =0' d2'))
  eq0-instep' {d1 = (·λ x1 [ τ1 ] d1) ∘ d1'} {d2 = (·λ x1 [ τ2 ] d2) ∘ d2'} (Eq0Ap (Eq0Lam eq0) eq1) ITLam compl wt1 wt2 = ([ d2' / x1 ] d2) , ITLam , eq0-subst' d1 d2 eq1 eq0
  eq0-instep' {d1 = (d1' ⟨ τ1 ==> τ3 ⇒ τ1' ==> τ3' ⟩) ∘ d5} {d2 = (d2' ⟨ τ2 ==> τ ⇒ τ2' ==> τ' ⟩) ∘ d4}
    (Eq0Ap (Eq0Cast eq0 (AlphaArr alphal alphal') (AlphaArr alphar alphar')) eq1) ITApCast compl wt1 (TAAp (TACast wt x₁ x₂ x₃) wt₁ x) = 
      ((d2' ∘ (d4 ⟨ τ2' ⇒ τ2 ⟩)) ⟨ τ ⇒ τ' ⟩) , ITApCast , Eq0Cast (Eq0Ap eq0 (Eq0Cast eq1 (alpha-sym alphal) (alpha-sym alphar))) alphal' alphar'
  eq0-instep' {d1 = ·Λ _ d1 < _ >} {d2 = ·Λ t d2 < τ2 >} (Eq0TAp (Eq0TLam eq0)) ITTLam (DCTAp x (DCTLam compl)) (TATAp x₁ (TATLam x₅ wt1) x₂) (TATAp x₃ (TATLam x₆ wt2) x₄) = Ihexp[ τ2 / t ] d2 , ITTLam , eq0-typsubst' d1 d2 compl x₁ x₃ eq0
  eq0-instep' {d1 = (d1 ⟨ ·∀ t τ ⇒ ·∀ t' τ' ⟩) < τ1 >} {d2 = (d2 ⟨ ·∀ t2 τ2 ⇒ ·∀ t2' τ2' ⟩) < τ3 >} 
    (Eq0TAp (Eq0Cast eq0 alphal alphar)) ITTApCast compl (TATAp x₅ (TACast wt1 x₇ x₈ x₉) x₆) (TATAp x (TACast wt x₂ x₃ x₄) x₁) = 
      (d2 < τ3 >) ⟨ Typ[ τ3 / t2 ] τ2 ⇒ Typ[ τ3 / t2' ] τ2' ⟩ , ITTApCast , Eq0Cast (Eq0TAp eq0) 
      (alpha-sub2 x₅ (alpha-wf (wf-ta {!   !} wf-empty-tctx (HCtx (λ ())) wt1)  (alpha-sym x₉)) x₇ alphal) 
      (alpha-sub2 x (alpha-wf (wf-ta {!   !} wf-empty-tctx (HCtx (λ ())) wt) (alpha-sym x₄)) x₂ alphar)
  eq0-instep' {d2 = d2 ⟨ τ2 ⇒ τ2' ⟩} (Eq0Cast eq0 alphal alphar) (ITCastID x) compl wt1 wt = d2 , ITCastID alphar , eq0
  eq0-instep' (Eq0Cast x₂ x₃ x₄) (ITCastSucceed x₅ x₆ x₇) (DCCast x () x₉ x₁₀) wt1 x₁
  eq0-instep' (Eq0Cast x₂ x₃ x₄) (ITCastFail x₅ x₆ x₇) (DCCast x () x₉ x₁₀) wt1 x₁
  eq0-instep' (Eq0Cast x₂ AlphaHole x₄) (ITGround x₅) (DCCast x () x₆ x₇) wt1 x₁
  eq0-instep' (Eq0Cast x₂ x₃ x₄) (ITExpand x₅) (DCCast x () x₇ x₈) wt1 x₁

  completeid-env : ∀{d d' ε} →
    d' dcompleteid →
    d' == ε ⟦ d ⟧ →
    d dcompleteid
  completeid-env dc FHOuter = dc
  completeid-env (DCAp dc dc₁) (FHAp1 env) = completeid-env dc env
  completeid-env (DCAp dc dc₁) (FHAp2 env) = completeid-env dc₁ env
  completeid-env (DCTAp x dc) (FHTAp env) = completeid-env dc env
  completeid-env (DCCast dc x x₁ x₂) (FHCast env) = completeid-env dc env

  wt-env : ∀{Δ d d' ε τ} →
    Δ , ∅ , ∅ ⊢ d :: τ →
    d == ε ⟦ d' ⟧ →
    Σ[ τ' ∈ htyp ] (Δ , ∅ , ∅ ⊢ d' :: τ')
  wt-env {τ = τ} wt FHOuter = τ , wt
  wt-env {τ = τ} (TAAp {τ1 = τ1} wt wt₁ x) (FHAp1 env₁) = wt-env wt env₁
  wt-env {τ = τ} (TAAp wt wt₁ x) (FHAp2 env₁) = wt-env wt₁ env₁
  wt-env {τ = τ} (TATAp x wt x₁) (FHTAp env₁) = wt-env wt env₁
  wt-env {τ = τ} (TANEHole x wt x₁ x₂ x₃) (FHNEHole env₁) = wt-env wt env₁
  wt-env {τ = τ} (TACast wt x x₁ x₂) (FHCast env₁) = wt-env wt env₁
  wt-env {τ = τ} (TAFailedCast wt x x₁ x₂ x₃) (FHFailedCast env₁) = wt-env wt env₁

  inst : ∀{A B : Set} → Σ[ a ∈ A ] (B) → B
  inst (x , y) = y

  eq0-step' : 
    ∀ {d1 d2 d1' τ τ'} →
    d1 dcompleteid →
    ∅ , ∅ , ∅ ⊢ d1 :: τ →
    ∅ , ∅ , ∅ ⊢ d2 :: τ' →
    d1 =0' d2 →
    d1 ↦ d1' →
    Σ[ d2' ∈ ihexp ] ((d2 ↦ d2') × (d1' =0' d2'))
  eq0-step' compl wt1 wt2 eq (Step ctx1 step1 ctx2) 
    with eq0-ctxin' eq ctx1
  ... | ( d3 , ε' , ctx3 , eq2 , eq3 )
    with wt-env wt1 ctx1 | wt-env wt2 ctx3
  ... | (_ , wt1') | (_ , wt2')
    with eq0-instep' eq2 step1 (completeid-env compl ctx1) wt1' wt2'
  ... | ( d4 , step2 , eq4 ) 
    with eq0-ctxout' eq4 eq3 ctx2 
  ... | d5 , eq5 , eq6 =  d5 , Step ctx3 step2 eq5 , eq6 

{-
  -- This was an attempt to remove the necessity of being well-typed, but we get stuck in showing the alpha equivalence for dcompleteid.
  -- It's probably avoidable but probably need to reformulate a few things for it to be so.

  -- This is a stronger version of the complete preservation theorem that doesn't require well-typing.
  -- These lemmas are mostly copy-pasted from complete-preservation
  lem-proj' : {x : Nat} {d : ihexp} { τ : htyp} → (·λ_[_]_ x τ d) dcompleteid → Σ[ y ∈ Nat ] (y == x)
  lem-proj' {x} (DCLam dc x₁) = x , refl

  cp-subst' : ∀ {x d1 d2} →
           d1 dcompleteid →
           d2 dcompleteid →
           ([ d2 / x ] d1) dcompleteid
  cp-subst' {x = y} (DCVar {x = x}) dc2 with natEQ x y
  cp-subst' DCVar dc2 | Inl refl = dc2
  cp-subst' DCVar dc2 | Inr x₂ = DCVar
  cp-subst' DCConst dc2 = DCConst
  cp-subst' {x = x} (DCLam {x = y} dc1 x₂) dc2 with natEQ y x
  cp-subst' (DCLam dc1 x₃) dc2 | Inl refl = DCLam dc1 x₃
  cp-subst' (DCLam dc1 x₃) dc2 | Inr x₂ = DCLam (cp-subst' dc1 dc2) x₃
  cp-subst' (DCAp dc1 dc2) dc3 = DCAp (cp-subst' dc1 dc3) (cp-subst' dc2 dc3)
  cp-subst' (DCCast dc1 x₁ x₂ x₃) dc2 = DCCast (cp-subst' dc1 dc2) x₁ x₂ x₃
  cp-subst' {d1 = ·Λ x₁ d1} (DCTLam x₂) x = DCTLam (cp-subst' x₂ x)
  cp-subst' {d1 = d1 < x₁ >} (DCTAp x₂ x₃) x = DCTAp x₂ (cp-subst' x₃ x)

  cp-typsubst' : ∀ {d t τ} →
           d dcompleteid →
           τ tcomplete →
           (Ihexp[ τ / t ] d) dcompleteid
  cp-typsubst' dc tc = {!   !}

  tcomplete-subst : ∀{τ t τ'} →
    τ tcomplete →
    τ' tcomplete →
    Typ[ τ' / t ] τ tcomplete
  tcomplete-subst TCBase tc' = TCBase
  tcomplete-subst {t = t} (TCVar {a = t'}) tc' with natEQ t t'
  ... | Inl refl = tc'
  ... | Inr neq = TCVar
  tcomplete-subst (TCArr tc tc₁) tc' = TCArr (tcomplete-subst tc tc') (tcomplete-subst tc₁ tc')
  tcomplete-subst {t = t} (TCForall {t = t'} tc) tc' with natEQ t t'
  ... | Inl refl = TCForall tc
  ... | Inr neq = TCForall (tcomplete-subst tc tc')

  -- Being able to prove this weakens the condition from well-typing to just type binder disjointness
  alpha-sub' : ∀{τ t1 τ1 t2 τ2} → τ τ1 tbinderstt-disjoint → τ τ2 tbinderstt-disjoint → ·∀ t1 τ1 =α ·∀ t2 τ2 → (Typ[ τ / t1 ] τ1) =α (Typ[ τ / t2 ] τ2)
  alpha-sub' = ?

  compl-complid-pres : ∀{d d'} →
    d tbinders-unique →
    d dcompleteid → 
    d ↦ d' →
    d' dcompleteid
  compl-complid-pres DCConst (Step FHOuter () FHOuter)
  compl-complid-pres DCVar (Step FHOuter () x₃)
  compl-complid-pres (DCLam _ _) (Step FHOuter () FHOuter)
  -- this case is a little more complicated than it feels like it ought to
  -- be, just from horsing around with agda implicit variables.
  compl-complid-pres (DCAp dc dc₁) (Step FHOuter ITLam FHOuter) with lem-proj' dc
  compl-complid-pres (DCAp dc dc₁) (Step FHOuter ITLam FHOuter) | x , refl with cp-subst' {x = x} dc dc₁
  ... | qq with natEQ x x
  compl-complid-pres (DCAp dc dc₁) (Step FHOuter ITLam FHOuter) | x , refl | DCLam qq x₁ | Inl refl = cp-subst' qq dc₁
  compl-complid-pres (DCAp dc dc₁) (Step FHOuter ITLam FHOuter) | x , refl | qq | Inr x₁ = abort (x₁ refl)
  compl-complid-pres (DCAp (DCCast dc (TCArr ll lr) (TCArr rl rr) (AlphaArr alphal alphar)) dc₁) (Step FHOuter ITApCast FHOuter) = DCCast (DCAp dc (DCCast dc₁ rl ll (alpha-sym alphal))) lr rr alphar
  compl-complid-pres (DCAp dc dc₁) (Step (FHAp1 x) x₁ (FHAp1 x₂)) = DCAp (compl-complid-pres dc (Step x x₁ x₂)) dc₁
  compl-complid-pres (DCAp dc dc₁) (Step (FHAp2 x) x₁ (FHAp2 x₂)) = DCAp dc (compl-complid-pres dc₁ (Step x x₁ x₂))
  compl-complid-pres (DCCast dc x x₁ alpha) (Step FHOuter (ITCastID alpha') FHOuter) = dc
  compl-complid-pres (DCCast dc () x₁ alpha) (Step FHOuter (ITCastSucceed g1 g2 alpha') FHOuter)
  compl-complid-pres (DCCast dc () x₁ alpha) (Step FHOuter (ITCastFail x₃ x₄ x₅) FHOuter)
  compl-complid-pres (DCCast dc x () alpha) (Step FHOuter (ITGround x₃) FHOuter)
  compl-complid-pres (DCCast dc () x₁ alpha) (Step FHOuter (ITExpand x₃) FHOuter)
  compl-complid-pres (DCCast dc x x₁ alpha) (Step (FHCast x₃) x₄ (FHCast x₅)) = DCCast (compl-complid-pres dc (Step x₃ x₄ x₅)) x x₁ alpha
  compl-complid-pres (DCTLam dc) (Step FHOuter () FHOuter)
  compl-complid-pres (DCTAp dc (DCTLam x)) (Step FHOuter ITTLam FHOuter) = cp-typsubst' x dc
  compl-complid-pres (DCTAp dc (DCCast x (TCForall x₁) (TCForall x₂) (AlphaForall x₃))) (Step FHOuter ITTApCast FHOuter) = DCCast (DCTAp dc x) (tcomplete-subst x₁ dc) (tcomplete-subst x₂ dc) {!   !}
  compl-complid-pres (DCTAp dc x) (Step (FHTAp x₁) x₂ (FHTAp x₃)) = DCTAp dc (compl-complid-pres x (Step x₁ x₂ x₃))
-}

  parametricity11_rec : 
    ∀ {τ τ' d1 d2 v1 } →
    d1 dcompleteid →
    d2 dcompleteid →
    ∅ , ∅ , ∅ ⊢ d1 :: τ → 
    ∅ , ∅ , ∅ ⊢ d2 :: τ' → 
    d1 =0' d2 →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ] ((d2 ↦* v2) × (v2 boxedval) × (v1 =0' v2))
  parametricity11_rec c1 c2 wt1 wt2 eq0 MSRefl bv = _ , MSRefl , eq0-boxedval' eq0 bv , eq0
  parametricity11_rec c1 c2 wt1 wt2 eq0 (MSStep x step) bv
    with eq0-step' c1 wt1 wt2 eq0 x
  ... | ( d2' , step2 , eq2 )
    with complete-preservation {!   !} (complid-compl c1) wt1 x | complete-preservation {!   !} (complid-compl c2) wt2 step2
  ... | (wt1' , c1') | (wt2' , c2')
    with parametricity11_rec (compl-wt-complid c1' wt1') (compl-wt-complid c2' wt2') wt1' wt2' eq2 step bv
  ... | ( v2 , steps2 , bv2 , eq3 ) = v2 , MSStep step2 steps2  , bv2 , eq3



  parametricity11 : 
    ∀ {e e' τ τ' d1 Δ Δ' d2 v1 } →
    e ecomplete →
    e' ecomplete →
    e =0e e' →
    ∅ , ∅ ⊢ e ⇒ τ ~> d1 ⊣ Δ →
    ∅ , ∅ ⊢ e' ⇒ τ' ~> d2 ⊣ Δ' →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ] ((d2 ↦* v2) × (v2 boxedval) × (v1 =0 v2))
  parametricity11 ec ec' eeq elab1 elab2 eval bv with dcompleteid-elab ec elab1 | dcompleteid-elab ec' elab2
  ... | (d1c , deltaempty) | (d2c , deltaempty') rewrite deltaempty rewrite deltaempty' =
    let (v2 , v2eval , v2bv , eq0') = parametricity11_rec d1c d2c (typed-elaboration-synth wf-empty-tctx elab1) (typed-elaboration-synth wf-empty-tctx elab2) (eq0-eq0' d1c d2c (eq0-elab-syn eeq elab1 elab2)) eval bv in
    (v2 , v2eval , v2bv , eq0'-eq0 eq0')



  -- parametricity22-lemma : 

--  p22_lemma1 : 
--    d1 ∘ d1' ↦ 

  -- =0 but we ignore casts when checking equality.
  mutual
    data _=0''_ : (d1 d2 : ihexp) → Set where 
      Eq0CastL : ∀{d1 d2 τ1 τ2} → d1 =0'' d2 → (d1 ⟨ τ1 ⇒ τ2 ⟩) =0'' d2
      Eq0FailedCastL : ∀{d1 d2 τ1 τ2} → d1 =0'' d2 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0'' d2
      Eq0NoLeft : ∀{d1 d2} → d1 =0''r d2 → d1 =0'' d2
    
    data _=0''r_ : (d1 d2 : ihexp) → Set where
      Eq0CastR : ∀{d1 d2 τ1 τ2} → d1 =0''r d2 → d1 =0''r (d2 ⟨ τ1 ⇒ τ2 ⟩)
      Eq0FailedCastR : ∀{d1 d2 τ1 τ2} → d1 =0''r d2 → d1 =0''r (d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
      Eq0NoCasts : ∀{d1 d2} → d1 =0''n d2 → d1 =0''r d2

    data _=0''n_ : (d1 d2 : ihexp) → Set where
      Eq0Const : c =0''n c
      Eq0Var : ∀{x} → (X x) =0''n (X x) 
      Eq0EHole : ∀{u θ θ' σ σ'} → ⦇-⦈⟨ u , θ , σ ⟩ =0''n ⦇-⦈⟨ u , θ' , σ' ⟩
      Eq0Lam : ∀{x d1 d2 τ1 τ2} → d1 =0 d2 → (·λ x [ τ1 ] d1) =0''n (·λ x [ τ2 ] d2)
      Eq0TLam : ∀{t d1 d2} → d1 =0 d2 → (·Λ t d1) =0''n (·Λ t d2)
      Eq0NEHole : ∀{u d1 d2 θ θ' σ σ'} → d1 =0 d2 →  (⦇⌜ d1 ⌟⦈⟨ u , θ , σ ⟩) =0''n (⦇⌜ d2 ⌟⦈⟨ u , θ' , σ' ⟩)
      Eq0Ap :  ∀{d1 d2 d3 d4} → d1 =0 d3 →  d2 =0 d4 →  (d1 ∘ d2) =0''n (d3 ∘ d4)
      Eq0TAp : ∀{d1 d2 τ1 τ2} → d1 =0 d2 → (d1 < τ1 >) =0''n (d2 < τ2 >)


  data _=0ε''_ : (ε1 ε2 : ectx) → Set where 
    Eq0Dot : ⊙ =0ε'' ⊙
    Eq0Ap1 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε'' ε2) → (d1 =0'' d2) → (ε1 ∘₁ d1) =0ε'' (ε2 ∘₁ d2)
    Eq0Ap2 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε'' ε2) → (d1 =0'' d2) → (d1 ∘₂ ε1) =0ε'' (d2 ∘₂ ε2)
    Eq0TAp : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε'' ε2) → (ε1 < τ1 >) =0ε'' (ε2 < τ2 >)
    Eq0NEHole : ∀{ε1 ε2 u θ θ' σ σ'} → (ε1 =0ε'' ε2) → (⦇⌜ ε1 ⌟⦈⟨ u , θ , σ ⟩) =0ε'' (⦇⌜ ε2 ⌟⦈⟨ u , θ' , σ' ⟩)
    Eq0CastL : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε'' ε2) → (ε1 ⟨ τ1 ⇒ τ2 ⟩) =0ε'' ε2
    Eq0CastR : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε'' ε2) → ε1 =0ε'' (ε2 ⟨ τ1 ⇒ τ2 ⟩)
    Eq0FailedCastL : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε'' ε2) → (ε1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0ε'' ε2
    Eq0FailedCastR : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε'' ε2) → ε1 =0ε'' (ε2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)


  eq0castl-lemma : ∀{d τ τ' d'} → 
    d =0'' d' →
    (d ⟨ τ ⇒ τ' ⟩) =0'' d'
  eq0castl-lemma (Eq0CastL eq0) = Eq0CastL (eq0castl-lemma eq0)
  eq0castl-lemma (Eq0NoLeft x) = Eq0CastL (Eq0NoLeft x)
  eq0castl-lemma (Eq0FailedCastL eq0) = Eq0CastL (Eq0FailedCastL eq0)

  eq0castr-lemma : ∀{d τ τ' d'} → 
    d =0'' d' →
    d =0'' (d' ⟨ τ ⇒ τ' ⟩)
  eq0castr-lemma (Eq0CastL eq0) = Eq0CastL (eq0castr-lemma eq0)
  eq0castr-lemma (Eq0NoLeft x) = Eq0NoLeft (Eq0CastR x)
  eq0castr-lemma (Eq0FailedCastL eq0) = Eq0FailedCastL (eq0castr-lemma eq0)


  eq0failedcastr-lemma : ∀{d τ τ' d'} → 
    d =0'' d' →
    d =0'' (d' ⟨ τ ⇒⦇-⦈⇏ τ' ⟩)
  eq0failedcastr-lemma (Eq0CastL eq0) = Eq0CastL (eq0failedcastr-lemma eq0)
  eq0failedcastr-lemma (Eq0NoLeft x) = Eq0NoLeft (Eq0FailedCastR x)
  eq0failedcastr-lemma (Eq0FailedCastL eq0) = Eq0FailedCastL (eq0failedcastr-lemma eq0)

  eq0castr-meaning : ∀{d d' d₀ τ τ'} →
    d =0''r d' →
    d ≠ (d₀ ⟨ τ ⇒ τ' ⟩) × d ≠ (d₀ ⟨ τ ⇒⦇-⦈⇏ τ' ⟩)
  eq0castr-meaning (Eq0NoCasts Eq0Const) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0NoCasts Eq0Var) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0NoCasts Eq0EHole) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0NoCasts (Eq0Lam x)) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0NoCasts (Eq0TLam x)) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0NoCasts (Eq0NEHole x)) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0NoCasts (Eq0Ap x x₁)) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0NoCasts (Eq0TAp x)) = (λ ()) , (λ ())
  eq0castr-meaning (Eq0CastR eq0) = eq0castr-meaning eq0
  eq0castr-meaning (Eq0FailedCastR eq0) = eq0castr-meaning eq0

  eq0castl-inverse : ∀{d τ τ' d'} → 
    (d ⟨ τ ⇒ τ' ⟩) =0'' d' →
    d =0'' d'
  eq0castl-inverse (Eq0CastL eq0) = eq0
  eq0castl-inverse (Eq0NoLeft x) = abort (π1 (eq0castr-meaning x) refl)

  eq0castr-inverse : ∀{d τ τ' d'} →
    d =0'' (d' ⟨ τ ⇒ τ' ⟩) →
    d =0'' d'
  eq0castr-inverse (Eq0CastL eq0) = Eq0CastL (eq0castr-inverse eq0)
  eq0castr-inverse (Eq0NoLeft (Eq0CastR x)) = Eq0NoLeft x
  eq0castr-inverse (Eq0FailedCastL eq0) = Eq0FailedCastL (eq0castr-inverse eq0)
  

  eq0-eq0'' : ∀{d d'} →
    d =0 d' →
    d =0'' d'
  eq0-eq0'' Eq0Const = Eq0NoLeft (Eq0NoCasts Eq0Const)
  eq0-eq0'' Eq0Var = Eq0NoLeft (Eq0NoCasts Eq0Var)
  eq0-eq0'' Eq0EHole = Eq0NoLeft (Eq0NoCasts Eq0EHole)
  eq0-eq0'' (Eq0Lam eq0) = Eq0NoLeft (Eq0NoCasts (Eq0Lam eq0))
  eq0-eq0'' (Eq0TLam eq0) = Eq0NoLeft (Eq0NoCasts (Eq0TLam eq0))
  eq0-eq0'' (Eq0NEHole eq0) = Eq0NoLeft (Eq0NoCasts (Eq0NEHole eq0))
  eq0-eq0'' (Eq0Ap eq0 eq1) = Eq0NoLeft (Eq0NoCasts (Eq0Ap eq0 eq1))
  eq0-eq0'' (Eq0TAp eq0) = Eq0NoLeft (Eq0NoCasts (Eq0TAp eq0))
  eq0-eq0'' (Eq0Cast eq0) = eq0castl-lemma (eq0castr-lemma (eq0-eq0'' eq0))
  eq0-eq0'' (Eq0FailedCast eq0) = Eq0FailedCastL (eq0failedcastr-lemma (eq0-eq0'' eq0))

  eq0''-val-eq0 : ∀{d d'} →
    d =0'' d' →
    d val →
    d' val →
    d =0 d'
  eq0''-val-eq0 eq0 v v' = {!   !}

  mutual
    eq0''n-sym : ∀{d d'} →
      d =0''n d' →
      d' =0''n d
    eq0''n-sym Eq0Const = Eq0Const
    eq0''n-sym Eq0Var = Eq0Var
    eq0''n-sym Eq0EHole = Eq0EHole
    eq0''n-sym (Eq0Lam x) = Eq0Lam (eq0-sym x)
    eq0''n-sym (Eq0TLam x) = Eq0TLam (eq0-sym x)
    eq0''n-sym (Eq0NEHole x) = Eq0NEHole (eq0-sym x)
    eq0''n-sym (Eq0Ap x x₁) = Eq0Ap (eq0-sym x) (eq0-sym x₁)
    eq0''n-sym (Eq0TAp x) = Eq0TAp (eq0-sym x)

    eq0''r-sym : ∀{d d'} →
      d =0''r d' →
      d' =0'' d
    eq0''r-sym (Eq0NoCasts x) = {!   !} -- Eq0NoCasts (eq0''n-sym x)
    eq0''r-sym (Eq0CastR eq0) = Eq0CastL (eq0''r-sym eq0)
    eq0''r-sym (Eq0FailedCastR eq0) = Eq0FailedCastL (eq0''r-sym eq0)
    
    eq0''-sym : ∀{d d'} →
      d =0'' d' →
      d' =0'' d
    eq0''-sym (Eq0CastL eq0) = eq0castr-lemma (eq0''-sym eq0)
    eq0''-sym (Eq0FailedCastL eq0) = eq0failedcastr-lemma (eq0''-sym eq0)
    eq0''-sym (Eq0NoLeft x) = eq0''r-sym x
{-
  eq0''-step-pres : ∀{d1 d2 τ τ' Δ d1' d2'} →
    Δ , ∅ , ∅ ⊢ d1 :: τ →
    Δ , ∅ , ∅ ⊢ d2 :: τ' →
    d1 =0'' d2 →
    d1 ↦* d1' →
    d2 ↦* d2' →
    d1' =0'' d2'
  eq0''-step-pres wt wt' Eq0Const (MSStep (Step FHOuter () _) _) step'
  eq0''-step-pres wt wt' Eq0Var (MSStep (Step FHOuter () _) _) step'
  eq0''-step-pres wt wt' Eq0EHole (MSStep (Step FHOuter () _) _) step'
  eq0''-step-pres wt wt' (Eq0Lam x) (MSStep (Step FHOuter () _) _) step'
  eq0''-step-pres wt wt' (Eq0TLam x) (MSStep (Step FHOuter () _) _) step'
  eq0''-step-pres (TANEHole x₆ wt x₇ x₈ x₉) (TANEHole x₁₀ wt' x₁₁ x₁₂ x₁₃) (Eq0NEHole eq0) (MSStep (Step (FHNEHole x) x₁ (FHNEHole x₂)) ms) (MSStep (Step (FHNEHole x₃) x₄ (FHNEHole x₅)) ms') = 
    eq0''-step-pres wt wt' eq0 {!   !} {!   !}
  eq0''-step-pres wt wt' (Eq0Ap eq0 x) step step' = {!   !}
  eq0''-step-pres wt wt' (Eq0TAp eq0) step step' = {!   !}
  eq0''-step-pres (TACast wt x₁ x₂ x₃) wt' (Eq0CastL eq0) (MSStep (Step FHOuter (ITCastID x) FHOuter) ms) step' = {! eq0  !}
  eq0''-step-pres (TACast wt wx₁ wx₂ wx₃) wt' (Eq0CastL eq0) (MSStep (Step FHOuter (ITCastSucceed x x₁ x₂) FHOuter) ms) step' = {!   !}
  eq0''-step-pres (TACast wt wx₁ wx₂ wx₃) wt' (Eq0CastL eq0) (MSStep (Step FHOuter (ITCastFail x x₁ x₂) FHOuter) ms) step' = {!   !}
  eq0''-step-pres (TACast wt wx₁ wx₂ wx₃) wt' (Eq0CastL eq0) (MSStep (Step FHOuter (ITGround x) FHOuter) ms) step' = {!   !}
  eq0''-step-pres (TACast wt wx₁ wx₂ wx₃) wt' (Eq0CastL eq0) (MSStep (Step FHOuter (ITExpand x) FHOuter) ms) step' = {!   !}
  eq0''-step-pres (TACast wt wx₁ wx₂ wx₃) wt' (Eq0CastL eq0) (MSStep (Step (FHCast x) x₁ (FHCast x₂)) ms) step' = {!   !}
  eq0''-step-pres wt wt' (Eq0CastR eq0) step step' = {!   !}
  eq0''-step-pres wt wt' (Eq0FailedCastL eq0) (MSStep (Step x step x') ms) step' = {!   !}
  eq0''-step-pres wt wt' (Eq0FailedCastR eq0) step (MSStep (Step x step' x') ms) = {!   !}
-}
  eq0-ctxin-lemma : 
    ∀ {d1 d2 d1' ε1} →
    d1 =0 d2 →
    d1 == ε1 ⟦ d1' ⟧ →
    Σ[ d2' ∈ ihexp ] Σ[ ε2 ∈ ectx ] ((d2 == ε2 ⟦ d2' ⟧) × (d1' =0 d2') × (ε1 =0ε'' ε2))
  eq0-ctxin-lemma eq FHOuter = _ , ⊙ , FHOuter , eq , Eq0Dot
  eq0-ctxin-lemma (Eq0NEHole eq) (FHNEHole ctxin) with eq0-ctxin-lemma eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHNEHole eq1 , eq2 , Eq0NEHole eq3
  eq0-ctxin-lemma (Eq0Ap eq eq₁) (FHAp1 ctxin) with eq0-ctxin-lemma eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHAp1 eq1 , eq2 , Eq0Ap1 eq3 (eq0-eq0'' eq₁)
  eq0-ctxin-lemma (Eq0Ap eq eq₁) (FHAp2 ctxin) with eq0-ctxin-lemma eq₁ ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHAp2 eq1 , eq2 , Eq0Ap2 eq3 (eq0-eq0'' eq)
  eq0-ctxin-lemma (Eq0TAp eq) (FHTAp ctxin) with eq0-ctxin-lemma eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 =  _ , _ , FHTAp eq1 , eq2 , Eq0TAp eq3
  eq0-ctxin-lemma (Eq0Cast eq) (FHCast ctxin) with eq0-ctxin-lemma eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHCast eq1 , eq2 , Eq0CastL (Eq0CastR eq3)
  eq0-ctxin-lemma (Eq0FailedCast eq) (FHFailedCast ctxin) with eq0-ctxin-lemma eq ctxin
  ... | d2' , ε2 , eq1 , eq2 , eq3 =  _ , _ , FHFailedCast eq1 , eq2 , Eq0FailedCastL (Eq0FailedCastR eq3)

  mutual
{-
    eq0-ctxin''n :
      ∀ {d1 d2 d1' ε1} →
      d1 =0''n d2 →
      d1 == ε1 ⟦ d1' ⟧ →
      Σ[ d2' ∈ ihexp ] Σ[ ε2 ∈ ectx ] ((d2 == ε2 ⟦ d2' ⟧) × (d1' =0'' d2') × (ε1 =0ε'' ε2))
    eq0-ctxin''n {d2 = d2} eq0 FHOuter = d2 , ⊙ , FHOuter , Eq0NoLeft (Eq0NoCasts eq0) , Eq0Dot
    eq0-ctxin''n (Eq0Ap {d4 = d4} x x₁) (FHAp1 ctxeq) with eq0-ctxin-lemma x ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , (ε2' ∘₁ d4) , FHAp1 ctxeq' , eq0-eq0'' eq0' , Eq0Ap1 ceq0' (eq0-eq0'' x₁)
    eq0-ctxin''n (Eq0Ap {d3 = d3} x x₁) (FHAp2 ctxeq) with eq0-ctxin-lemma x₁ ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , (d3 ∘₂ ε2') , FHAp2 ctxeq' , eq0-eq0'' eq0' , Eq0Ap2 ceq0' (eq0-eq0'' x)
    eq0-ctxin''n (Eq0TAp {τ2 = τ2} x) (FHTAp ctxeq) with eq0-ctxin-lemma x ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , (ε2' < τ2 >) , FHTAp ctxeq' , eq0-eq0'' eq0' , Eq0TAp ceq0'
    eq0-ctxin''n (Eq0NEHole x) (FHNEHole ctxeq) with eq0-ctxin-lemma x ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , _ , FHNEHole ctxeq' , eq0-eq0'' eq0' , Eq0NEHole ceq0'

    eq0-ctxin''r : 
      ∀ {d1 d2 d1' ε1} →
      d1 =0''r d2 →
      d1 == ε1 ⟦ d1' ⟧ →
      Σ[ d2' ∈ ihexp ] Σ[ ε2 ∈ ectx ] ((d2 == ε2 ⟦ d2' ⟧) × (d1' =0'' d2') × (ε1 =0ε'' ε2))
    eq0-ctxin''r {d2 = d2} eq0 FHOuter = d2 , ⊙ , FHOuter , Eq0NoLeft eq0 , Eq0Dot
    eq0-ctxin''r (Eq0CastR {τ1 = τ1} {τ2 = τ2} eq0) ctxeq with eq0-ctxin''r eq0 ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , (ε2' ⟨ τ1 ⇒ τ2 ⟩) , FHCast ctxeq' , eq0' , Eq0CastR ceq0'
    eq0-ctxin''r (Eq0FailedCastR {τ1 = τ1} {τ2 = τ2} eq0) ctxeq with eq0-ctxin''r eq0 ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , (ε2' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) , FHFailedCast ctxeq' , eq0' , Eq0FailedCastR ceq0'
    eq0-ctxin''r (Eq0NoCasts x) ctxeq = eq0-ctxin''n x ctxeq

    eq0-ctxin'' : 
      ∀ {d1 d2 d1' ε1} →
      d1 =0'' d2 →
      d1 == ε1 ⟦ d1' ⟧ →
      Σ[ d2' ∈ ihexp ] Σ[ ε2 ∈ ectx ] ((d2 == ε2 ⟦ d2' ⟧) × (d1' =0'' d2') × (ε1 =0ε'' ε2))
    eq0-ctxin'' {d2 = d2} eq0 FHOuter = d2 , ⊙ , FHOuter , eq0 , Eq0Dot
    eq0-ctxin'' (Eq0CastL eq0) (FHCast ctxeq) with eq0-ctxin'' eq0 ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , ε2' , ctxeq' , eq0' , Eq0CastL ceq0'
    eq0-ctxin'' (Eq0NoLeft x) ctxeq with eq0-ctxin''r x  ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , ε2' , ctxeq' , eq0' , ceq0'
    eq0-ctxin'' (Eq0FailedCastL eq0) (FHFailedCast ctxeq) with eq0-ctxin'' eq0 ctxeq
    ... | (d2' , ε2' , ctxeq' , eq0' , ceq0') = d2' , ε2' , ctxeq' , eq0' , Eq0FailedCastL ceq0'
-}
    eq0-ctxin''n : 
      ∀ {d1 d2 d1' d2' ε1 ε2} →
      d1 =0''n d2 →
      d1 == ε1 ⟦ d1' ⟧ →
      d2 == ε2 ⟦ d2' ⟧ →
      (d1' =0'' d2') × (ε1 =0ε'' ε2)
    eq0-ctxin''n eq0 ctxeq ctxeq' = {!   !}

    eq0-ctxin'' : 
      ∀ {d1 d2 d1' d2' ε1 ε2} →
      d1 =0'' d2 →
      d1 == ε1 ⟦ d1' ⟧ →
      d2 == ε2 ⟦ d2' ⟧ →
      (d1' =0'' d2') × (ε1 =0ε'' ε2)
    eq0-ctxin'' eq0 ctxeq ctxeq' = {!   !}

  eq0-ctxout'' : 
    ∀ {d1 d1' d2 d2' ε1 ε2} →
    d1' =0'' d2' →
    ε1 =0ε'' ε2 →
    d1 == ε1 ⟦ d1' ⟧ →
    d2 == ε2 ⟦ d2' ⟧ →
    d1 =0'' d2
  eq0-ctxout'' eq0 ceq0 ctxeq ctxeq' = {!  ctxeq !}

{-
  mutual
    eq0-subst''n : 
      ∀ {x d1 d2} →
      (d3 d4 : ihexp) →
      d1 =0'' d2 →
      d3 =0''n d4 →
      ([ d1 / x ] d3) =0'' ([ d2 / x ] d4)
    eq0-subst''n .c .c eq0 Eq0Const = Eq0NoLeft (Eq0NoCasts Eq0Const)
    eq0-subst''n {x = x} (X a) (X a) eq0 Eq0Var with natEQ a x
    ... | Inl refl = eq0
    ... | Inr neq = Eq0NoLeft (Eq0NoCasts Eq0Var)
    eq0-subst''n .(⦇-⦈⟨ _ , _ , _ ⟩) .(⦇-⦈⟨ _ , _ , _ ⟩) eq0 Eq0EHole = Eq0NoLeft (Eq0NoCasts Eq0EHole)
    eq0-subst''n {x = x} (·λ a [ _ ] d3) (·λ a [ _ ] d4) eq0 (Eq0Lam eq0') with natEQ a x
    ... | Inl refl = Eq0NoLeft (Eq0NoCasts (Eq0Lam eq0'))
    ... | Inr neq = Eq0NoLeft (Eq0NoCasts (Eq0Lam {! (eq0-subst d3 d4 ? ?) !}))
    eq0-subst''n (·Λ _ d3) (·Λ _ d4) eq0 (Eq0TLam x) = {!   !}
    eq0-subst''n (⦇⌜ d3 ⌟⦈⟨ _ , _ , _ ⟩) (⦇⌜ d4 ⌟⦈⟨ _ , _ , _ ⟩) eq0 (Eq0NEHole x) = {!   !}
    eq0-subst''n (d3 ∘ d3') (d4 ∘ d4') eq0 (Eq0Ap x x₁) = {!   !}
    eq0-subst''n (d3 < _ >) (d4 < _ >) eq0 (Eq0TAp x) = {!   !}
    
    eq0-subst''r : 
      ∀ {x d1 d2} →
      (d3 d4 : ihexp) →
      d1 =0'' d2 →
      d3 =0''r d4 →
      ([ d1 / x ] d3) =0'' ([ d2 / x ] d4)
    eq0-subst''r d3 (d4 ⟨ _ ⇒ _ ⟩) eq0 (Eq0CastR eq0') = eq0castr-lemma (eq0-subst''r d3 d4 eq0 eq0')
    eq0-subst''r d3 (d4 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) eq0 (Eq0FailedCastR eq0') = eq0failedcastr-lemma (eq0-subst''r d3 d4 eq0 eq0')
    eq0-subst''r d3 d4 eq0 (Eq0NoCasts x) = eq0-subst''n d3 d4 eq0 x
    
    eq0-subst'' : 
      ∀ {x d1 d2} →
      (d3 d4 : ihexp) →
      d1 =0'' d2 →
      d3 =0'' d4 →
      ([ d1 / x ] d3) =0'' ([ d2 / x ] d4)
    eq0-subst'' (d3 ⟨ _ ⇒ _ ⟩) d4 eq0 (Eq0CastL eq0') = Eq0CastL (eq0-subst'' d3 d4 eq0 eq0')
    eq0-subst'' (d3 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) d4 eq0 (Eq0FailedCastL eq0') = Eq0FailedCastL (eq0-subst'' d3 d4 eq0 eq0')
    eq0-subst'' d3 d4 eq0 (Eq0NoLeft x) = eq0-subst''r d3 d4 eq0 x
-}


  mutual
    parametricity22-lemma-nocasts : ∀{d1 d2 d1' d2'} →
      d1 =0''n d2 →
      d1 →> d1' →
      d2 →> d2' →
      d1' =0 d2'
    parametricity22-lemma-nocasts (Eq0Ap {d1 = ·λ _ [ _ ] d1} {d2 = d2} {d3 = ·λ _ [ _ ] d3} {d4 = d4} (Eq0Lam x) x₁) ITLam ITLam = eq0-subst d1 d3 x₁ x
    parametricity22-lemma-nocasts (Eq0Ap (Eq0Cast x) x₁) ITApCast ITApCast = (Eq0Cast (Eq0Ap x (Eq0Cast x₁)))
    parametricity22-lemma-nocasts (Eq0TAp {d1 = ·Λ _ d1} {d2 = ·Λ _ d2} (Eq0TLam x)) ITTLam ITTLam = eq0-typsubst d1 d2 x
    parametricity22-lemma-nocasts (Eq0TAp (Eq0Cast x)) ITTApCast ITTApCast = (Eq0Cast (Eq0TAp x))

    parametricity22-lemma : ∀{d1 d2 d1' d2'} →
      d1 =0'' d2 →
      d1 →> d1' →
      d2 →> d2' →
      d1' =0'' d2' + d1 =0'' d2' + d1' =0'' d2
    parametricity22-lemma (Eq0CastL eq0) (ITCastID x) step' = Inr (Inr eq0)
    parametricity22-lemma (Eq0CastL (Eq0CastL eq0)) (ITCastSucceed x x₁ x₂) step' = Inr (Inr eq0)
    parametricity22-lemma (Eq0CastL (Eq0NoLeft x₃)) (ITCastSucceed x x₁ x₂) step' = abort (π1 (eq0castr-meaning x₃) refl)
    parametricity22-lemma (Eq0CastL (Eq0CastL eq0)) (ITCastFail x x₁ x₂) step' = Inr (Inr (Eq0FailedCastL eq0))
    parametricity22-lemma (Eq0CastL (Eq0NoLeft eq0)) (ITCastFail x x₁ x₂) step' = abort (π1 (eq0castr-meaning eq0) refl)
    parametricity22-lemma (Eq0CastL eq0) (ITGround x) step' = Inr (Inr (Eq0CastL (Eq0CastL eq0)))
    parametricity22-lemma (Eq0CastL eq0) (ITExpand x) step' = Inr (Inr (Eq0CastL (Eq0CastL eq0)))
    parametricity22-lemma (Eq0NoLeft (Eq0CastR x)) step (ITCastID x₁) = Inr (Inl (Eq0NoLeft x))
    parametricity22-lemma (Eq0NoLeft (Eq0CastR (Eq0CastR x))) step (ITCastSucceed x₁ x₂ x₃) = Inr (Inl (Eq0NoLeft x))
    parametricity22-lemma (Eq0NoLeft (Eq0CastR (Eq0CastR x))) step (ITCastFail x₁ x₂ x₃) = Inr (Inl (Eq0NoLeft (Eq0FailedCastR x)))
    parametricity22-lemma (Eq0NoLeft (Eq0CastR (Eq0NoCasts ()))) step (ITCastFail x₁ x₂ x₃)
    parametricity22-lemma (Eq0NoLeft (Eq0CastR x)) step (ITGround x₁) = Inr (Inl (Eq0NoLeft (Eq0CastR (Eq0CastR x))))
    parametricity22-lemma (Eq0NoLeft (Eq0CastR x)) step (ITExpand x₁) = Inr (Inl (Eq0NoLeft (Eq0CastR (Eq0CastR x))))
    parametricity22-lemma (Eq0NoLeft (Eq0NoCasts x)) step step' = Inl (eq0-eq0'' (parametricity22-lemma-nocasts x step step'))

  parametricity22-lemma-ctx : ∀{d1 d2 d1' d2'} →
      d1 =0'' d2 →
      d1 ↦ d1' →
      d2 ↦ d2' →
      d1' =0'' d2' + d1 =0'' d2' + d1' =0'' d2
  parametricity22-lemma-ctx eq0 (Step x1 step x2) (Step x1' step' x2') 
    with eq0-ctxin'' eq0 x1 x1'
  ... | ( eq0' , ctxeq' )
    with parametricity22-lemma eq0' step step'
  ... | Inl both = Inl (eq0-ctxout'' both ctxeq' x2 x2')
  ... | Inr (Inl left) = Inr (Inl (eq0-ctxout'' left ctxeq' x1 x2'))
  ... | Inr (Inr right) = Inr (Inr (eq0-ctxout'' right ctxeq' x2 x1'))
--    with eq0-ctxout'' eq4 eq3 x2
--  ... | d5 , eq5 , eq6 = ?

{-
  failedcast-never-boxedval : ∀{d τ τ' v} →
    v boxedval →
    ¬ ((d ⟨ τ ⇒⦇-⦈⇏ τ' ⟩) ↦* v)
  failedcast-never-boxedval (BVVal ()) MSRefl
  failedcast-never-boxedval bv (MSStep (Step (FHFailedCast x) x₁ (FHFailedCast x₂)) step) = failedcast-never-boxedval bv step

  gnd-wf : ∀{Θ τ τ'} →
    Θ ⊢ τ wf →
    τ ▸gnd τ' →
    Θ ⊢ τ' wf
  gnd-wf wf gnd = {!   !}
-}


  mutual
    parametricity22-onesidedn : ∀{d1 v2 d1'} → 
      d1 =0''n v2 →
      v2 boxedval →
      d1 ↦ d1' →
      d1' =0'' v2
    parametricity22-onesidedn (Eq0NEHole x) (BVVal ()) (Step (FHNEHole x₂) x₁ (FHNEHole x₃))
    parametricity22-onesidedn (Eq0Ap x x₂) (BVVal ()) (Step FHOuter x₁ FHOuter)
    parametricity22-onesidedn (Eq0Ap x x₂) (BVVal ()) (Step (FHAp1 x₃) x₁ (FHAp1 x₄))
    parametricity22-onesidedn (Eq0Ap x x₂) (BVVal ()) (Step (FHAp2 x₃) x₁ (FHAp2 x₄))
    parametricity22-onesidedn (Eq0TAp x) (BVVal ()) (Step FHOuter x₁ FHOuter)
    parametricity22-onesidedn (Eq0TAp x) (BVVal ()) (Step (FHTAp x₂) x₁ (FHTAp x₃))

    parametricity22-onesidedr : ∀{d1 v2 d1'} → 
      d1 =0''r v2 →
      v2 boxedval →
      d1 ↦ d1' →
      d1' =0'' v2
    parametricity22-onesidedr (Eq0NoCasts x) bv step = parametricity22-onesidedn x bv step
    parametricity22-onesidedr (Eq0CastR eq0) (BVArrCast x bv) step = eq0castr-lemma (parametricity22-onesidedr eq0 bv step)
    parametricity22-onesidedr (Eq0CastR eq0) (BVForallCast x bv) step = eq0castr-lemma (parametricity22-onesidedr eq0 bv step)
    parametricity22-onesidedr (Eq0CastR eq0) (BVHoleCast x bv) step = eq0castr-lemma (parametricity22-onesidedr eq0 bv step)
    parametricity22-onesidedr (Eq0FailedCastR eq0) (BVVal ()) step

    parametricity22-onesided : ∀{d1 v2 d1'} → 
      d1 =0'' v2 →
      v2 boxedval →
      d1 ↦ d1' →
      d1' =0'' v2
    parametricity22-onesided (Eq0CastL eq0) bv (Step FHOuter (ITCastID x) FHOuter) = eq0
    parametricity22-onesided (Eq0CastL (Eq0CastL eq0)) bv (Step FHOuter (ITCastSucceed x x₁ x₂) FHOuter) = eq0
    parametricity22-onesided (Eq0CastL (Eq0NoLeft x₃)) bv (Step FHOuter (ITCastSucceed x x₁ x₂) FHOuter) = abort (π1 (eq0castr-meaning x₃) refl)
    parametricity22-onesided (Eq0CastL (Eq0CastL eq0)) bv (Step FHOuter (ITCastFail x x₁ x₂) FHOuter) = Eq0FailedCastL eq0
    parametricity22-onesided (Eq0CastL (Eq0NoLeft x₃)) bv (Step FHOuter (ITCastFail x x₁ x₂) FHOuter) = abort (π1 (eq0castr-meaning x₃) refl)
    parametricity22-onesided (Eq0CastL eq0) bv (Step FHOuter (ITGround x) FHOuter) = Eq0CastL (Eq0CastL eq0)
    parametricity22-onesided (Eq0CastL eq0) bv (Step FHOuter (ITExpand x) FHOuter) = Eq0CastL (Eq0CastL eq0)
    parametricity22-onesided (Eq0CastL eq0) bv (Step (FHCast x) x₁ (FHCast x₂)) =
      Eq0CastL (parametricity22-onesided eq0 bv (Step x x₁ x₂))
    parametricity22-onesided (Eq0FailedCastL eq0) bv (Step (FHFailedCast x) x₁ (FHFailedCast x₂)) = Eq0FailedCastL (parametricity22-onesided eq0 bv (Step x x₁ x₂))
    parametricity22-onesided {v2 = v2 ⟨ x₂ ⇒⦇-⦈⇏ x₃ ⟩} (Eq0NoLeft (Eq0FailedCastR x₄)) (BVVal ()) step
    parametricity22-onesided (Eq0NoLeft (Eq0CastR x)) bv step = parametricity22-onesidedr (Eq0CastR x) bv step
    parametricity22-onesided (Eq0NoLeft (Eq0NoCasts x)) bv step = parametricity22-onesidedn x bv step

{-
  parametricity22-incast : ∀{d1 d1' d1in d1in' d1out d1out' τ τ' v2 ε} →
    d1 == ε ⟨ τ ⇒ τ' ⟩ ⟦ d1in ⟧ →
    d1' == ε ⟨ τ ⇒ τ' ⟩ ⟦ d1in' ⟧ →
    d1 =0'' v2 →
    v2 boxedval →
    d1in →> d1in' →
    d1' =0'' v2
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv ITLam = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv ITTLam = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv (ITCastID x) = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv (ITCastSucceed x x₁ x₂) = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv (ITCastFail x x₁ x₂) = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv ITApCast = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv ITTApCast = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv (ITGround x) = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv (ITExpand x) = {!   !}
  parametricity22-incast (FHCast out) (FHCast out') (Eq0NoLeft x) bv step = abort (π1 (eq0castr-meaning x) refl)
  parametricity22-incast (FHCast out) (FHCast out') (Eq0FailedCastR x) bv step = abort (π1 (eq0castr-meaning x) refl)
--  parametricity22-incast (FHCast out) (FHCast out') (Eq0CastL eq0) bv (FHCast inn) (FHCast inn') step = Eq0CastL (parametricity22-incast out out' eq0 bv inn inn' step)
-}

  -- We have to do some fiddling to make the termination checker happy.
  tracelength : ∀{d d'} →
    d ↦* d' → Nat
  tracelength MSRefl = 0
  tracelength (MSStep _ ms) = 1+ (tracelength ms)

  parametricity22-gas :
    ∀{d1 d2 v1 v2} →
    d1 =0'' d2 →
    (ms : d1 ↦* v1) →
    (ms' : d2 ↦* v2) →
    v1 boxedval →
    v2 boxedval →
    (n : Nat) →
    ((tracelength ms) nat+ (tracelength ms')) < n →
    v1 =0'' v2
  parametricity22-gas _ _ _ _ _ 0 ()
  parametricity22-gas eq0 MSRefl MSRefl bv bv' n term = eq0
  parametricity22-gas eq0 MSRefl (MSStep step' ms') bv bv' (1+ n) (LTS term) rewrite ! (nat+Z (tracelength ms')) = eq0''-sym (parametricity22-gas (parametricity22-onesided (eq0''-sym eq0) bv step') ms' MSRefl bv' bv n term)
  parametricity22-gas eq0 (MSStep step ms) MSRefl bv bv' (1+ n) (LTS term) = 
    parametricity22-gas (parametricity22-onesided eq0 bv' step) ms MSRefl bv bv' n term
  parametricity22-gas eq0 (MSStep step ms) (MSStep step' ms') bv bv' (1+ n) (LTS term) with parametricity22-lemma-ctx eq0 step step'
  ... | Inr (Inl left) rewrite nat+1+ (tracelength ms) (tracelength ms') = parametricity22-gas left (MSStep step ms) ms' bv bv' n term
  ... | Inr (Inr right) = parametricity22-gas right ms (MSStep step' ms') bv bv' n term
  ... | Inl both with n
  ...   | 1+ n' rewrite nat+1+ (tracelength ms) (tracelength ms') = parametricity22-gas both ms ms' bv bv' n' (lt-1+-inj term)
  ...   | Z with term
  ...     | ()

  -- The version without the termination structure.
  parametricity22 :
    ∀{d1 d2 v1 v2} →
    d1 =0'' d2 →
    (ms : d1 ↦* v1) →
    (ms' : d2 ↦* v2) →
    v1 boxedval →
    v2 boxedval →
    v1 =0'' v2
  parametricity22 eq0 ms ms' bv bv' = parametricity22-gas eq0 ms ms' bv bv' (1+ ((tracelength ms) nat+ (tracelength ms'))) lt-1+

{-  parametricity11 complete wt eq MSRefl bv = _ , MSRefl , {! eq0-boxedval' eq bv !} , eq 
  parametricity11 complete wt eq (MSStep step steps) bv 
    with eq0-step eq step 
  ... | ( d2' , step2 , eq2 )
    with (parametricity11 complete {!   !} eq2 steps bv)
  ... | ( v2 , steps2 , bv2 , eq3 ) = v2 , MSStep step2 steps2  , bv2 , eq3
      
-}
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
               