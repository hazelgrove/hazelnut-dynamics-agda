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

{-
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
-}

{-
  eq0-typsubst : 
    ∀ {t τ1 τ2} →
    (d1 d2 : ihexp) →
    d1 dcompleteid →
    d1 =0 d2 →
    (Ihexp[ τ1 / t ] d1) =0 (Ihexp[ τ2 / t ] d2)
  eq0-typsubst .c .c _ Eq0Const = Eq0Const
  eq0-typsubst .(X _) .(X _) _ Eq0Var = Eq0Var
  eq0-typsubst .(⦇-⦈⟨ _ ⟩) .(⦇-⦈⟨ _ ⟩) _ Eq0EHole = Eq0EHole
  eq0-typsubst (·λ _ [ _ ] d1) (·λ _ [ _ ] d2) compl (Eq0Lam eq) = Eq0Lam (eq0-typsubst d1 d2 {!   !} eq)
  eq0-typsubst {t = t} (·Λ t' d1) (·Λ t' d2) _ (Eq0TLam eq) with natEQ t t' 
  ... | Inl refl = Eq0TLam eq
  ... | Inr x = Eq0TLam (eq0-typsubst d1 d2 {!   !} eq)
  eq0-typsubst .(⦇⌜ _ ⌟⦈⟨ _ ⟩) .(⦇⌜ _ ⌟⦈⟨ _ ⟩) _ (Eq0NEHole eq) = {!   !}
  eq0-typsubst (d1 ∘ d2) (d3 ∘ d4) _ (Eq0Ap eq eq₁) = Eq0Ap (eq0-typsubst d1 d3 {!   !} eq) (eq0-typsubst d2 d4 {!   !} eq₁)
  eq0-typsubst (d1 < _ >) (d2 < _ >) _ (Eq0TAp eq) = Eq0TAp (eq0-typsubst d1 d2 {!   !} eq)
  eq0-typsubst (d1 ⟨ _ ⇒ _ ⟩) (d2 ⟨ _ ⇒ _ ⟩) _ (Eq0Cast eq) = {!  Eq0Cast (eq0-typsubst d1 d2 ? eq) !}
  eq0-typsubst (d1 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) (d2 ⟨ _ ⇒⦇-⦈⇏ _ ⟩) _ (Eq0FailedCast eq) = {!   !}
-}

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
  eq0-subst' (⦇-⦈⟨ u3 ⟩) (⦇-⦈⟨ u5 ⟩) eq0 Eq0EHole = Eq0EHole -- Eq0NEHole (eq0-subst' ? ? eq0 ?)
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
            d dcompleteid
  dcompleteid-elab ec elab with complete-elaboration-synth empty-ctx-gcomplete ec elab | typed-elaboration-synth wf-empty-tctx elab
  ... | (dc , tc , dempty) | wt = compl-wt-complid dc wt

  
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

  consist-wf : ∀{Θ τ τ'} → Θ ⊢ τ wf → τ ~ τ' → Θ ⊢ τ' wf
  consist-wf wf consist = {!   !}

  eq0-instep' : 
    ∀ {d1 d2 d1' Δ τ τ'} →
    d1 =0' d2 →
    d1 →> d1' →
    d1 dcompleteid →
    Δ , ∅ , ∅ ⊢ d1 :: τ →
    Δ , ∅ , ∅ ⊢ d2 :: τ' →
    Σ[ d2' ∈ ihexp ] ((d2 →> d2') × (d1' =0' d2'))
  eq0-instep' {d1 = (·λ x1 [ τ1 ] d1) ∘ d1'} {d2 = (·λ x1 [ τ2 ] d2) ∘ d2'} (Eq0Ap (Eq0Lam eq0) eq1) ITLam compl wt1 wt2 = ([ d2' / x1 ] d2) , ITLam , eq0-subst' d1 d2 eq1 eq0
  eq0-instep' {d1 = (d1' ⟨ τ1 ==> τ3 ⇒ τ1' ==> τ3' ⟩) ∘ d5} {d2 = (d2' ⟨ τ2 ==> τ ⇒ τ2' ==> τ' ⟩) ∘ d4}
    (Eq0Ap (Eq0Cast eq0 (AlphaArr alphal alphal') (AlphaArr alphar alphar')) eq1) ITApCast compl wt1 (TAAp (TACast wt x₁ x₂ x₃) wt₁ x) = 
      ((d2' ∘ (d4 ⟨ τ2' ⇒ τ2 ⟩)) ⟨ τ ⇒ τ' ⟩) , ITApCast , Eq0Cast (Eq0Ap eq0 (Eq0Cast eq1 (alpha-sym alphal) (alpha-sym alphar))) alphal' alphar'
  eq0-instep' {d1 = ·Λ _ d1 < _ >} {d2 = ·Λ t d2 < τ2 >} (Eq0TAp (Eq0TLam eq0)) ITTLam (DCTAp x (DCTLam compl)) (TATAp x₁ (TATLam x₅ wt1) x₂) (TATAp x₃ (TATLam x₆ wt2) x₄) = Ihexp[ τ2 / t ] d2 , ITTLam , eq0-typsubst' d1 d2 compl x₁ x₃ eq0
  eq0-instep' {d1 = (d1 ⟨ ·∀ t τ ⇒ ·∀ t' τ' ⟩) < τ1 >} {d2 = (d2 ⟨ ·∀ t2 τ2 ⇒ ·∀ t2' τ2' ⟩) < τ3 >} 
    (Eq0TAp (Eq0Cast eq0 alphal alphar)) ITTApCast compl (TATAp x₅ (TACast wt1 x₇ x₈ x₉) x₆) (TATAp x (TACast wt x₂ x₃ x₄) x₁) = 
      (d2 < τ3 >) ⟨ Typ[ τ3 / t2 ] τ2 ⇒ Typ[ τ3 / t2' ] τ2' ⟩ , ITTApCast , Eq0Cast (Eq0TAp eq0) 
      (alpha-sub2 x₅ (alpha-wf (wf-ta {!   !} wf-empty-tctx {!   !} wt1)  (alpha-sym x₉)) x₇ alphal) 
      (alpha-sub2 x (consist-wf x₂ (~sym x₃)) x₂ alphar)
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
    ∀ {d1 d2 d1' τ τ' Δ} →
    d1 dcompleteid →
    Δ , ∅ , ∅ ⊢ d1 :: τ →
    Δ , ∅ , ∅ ⊢ d2 :: τ' →
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

  compl-complid-pres : ∀{d d' τ Δ} →
    d dcompleteid → 
    Δ , ∅ , ∅ ⊢ d :: τ → 
    d ↦ d' →
    d' dcompleteid
  compl-complid-pres compl wt step with complete-preservation {!   !} (complid-compl compl) wt step
  ... | (wt' , compl') = compl-wt-complid compl' wt' 

  parametricity11_rec : 
    ∀ {τ τ' d1 Δ d2 v1 } →
    d1 dcompleteid →
    d2 dcompleteid →
    Δ , ∅ , ∅ ⊢ d1 :: τ → 
    Δ , ∅ , ∅ ⊢ d2 :: τ' → 
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
    ∀ {e e' τ τ' d1 Δ d2 v1 } →
    e ecomplete →
    e' ecomplete →
    e =0e e' →
    ∅ , ∅ ⊢ e ⇒ τ ~> d1 ⊣ Δ →
    ∅ , ∅ ⊢ e' ⇒ τ' ~> d2 ⊣ Δ →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ] ((d2 ↦* v2) × (v2 boxedval) × (v1 =0 v2))
  parametricity11 ec ec' eeq elab1 elab2 eval bv =
    let d1c = (dcompleteid-elab ec elab1) in
    let d2c = (dcompleteid-elab ec' elab2) in
    let (v2 , v2eval , v2bv , eq0') = parametricity11_rec d1c d2c (typed-elaboration-synth wf-empty-tctx elab1) (typed-elaboration-synth wf-empty-tctx elab2) (eq0-eq0' d1c d2c (eq0-elab-syn eeq elab1 elab2)) eval bv in
    (v2 , v2eval , v2bv , eq0'-eq0 eq0')
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
       