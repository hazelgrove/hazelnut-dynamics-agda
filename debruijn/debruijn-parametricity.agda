open import Nat
open import Prelude
open import debruijn.debruijn-core-type
open import debruijn.debruijn-core-exp
open import debruijn.debruijn-core-subst
open import debruijn.debruijn-core

open import debruijn.debruijn-lemmas-index
open import debruijn.debruijn-lemmas-consistency
open import debruijn.debruijn-lemmas-prec
open import debruijn.debruijn-lemmas-meet
open import debruijn.debruijn-lemmas-subst
open import debruijn.debruijn-lemmas-wf
open import debruijn.debruijn-lemmas-complete

open import debruijn.debruijn-typed-elaboration
open import debruijn.debruijn-complete-elaboration
-- open import debruijn.debruijn-preservation
open import debruijn.debruijn-complete-preservation

module debruijn.debruijn-parametricity where

  -- preservation statement included rather than allow unsolved metas
  preservation : ∀ { d d' τ } →  
    ∅ ⊢ d :: τ →
    d ↦ d' →
    ∅ ⊢ d' :: τ
  preservation = {!   !}

  data _=0_ : (d1 d2 : ihexp) → Set where 
    Eq0Const : c =0 c
    Eq0Var : ∀{x} → (X x) =0 (X x) 
    Eq0EHole : ⦇-⦈ =0 ⦇-⦈
    Eq0Lam : ∀{d1 d2 τ1 τ2} → d1 =0 d2 → (·λ[ τ1 ] d1) =0 (·λ[ τ2 ] d2)
    Eq0TLam : ∀{d1 d2} → d1 =0 d2 → (·Λ d1) =0 (·Λ d2)
    Eq0NEHole : ∀{d1 d2} → d1 =0 d2 → ⦇⌜ d1 ⌟⦈ =0 ⦇⌜ d2 ⌟⦈
    Eq0Ap :  ∀{d1 d2 d3 d4} → d1 =0 d3 →  d2 =0 d4 →  (d1 ∘ d2) =0 (d3 ∘ d4)
    Eq0TAp : ∀{d1 d2 τ1 τ2} → d1 =0 d2 → (d1 < τ1 >) =0 (d2 < τ2 >)
    Eq0Cast : ∀{d1 d2 τ1 τ2 τ3 τ4} → d1 =0 d2 → (d1 ⟨ τ1 ⇒ τ2 ⟩) =0 (d2 ⟨ τ3 ⇒ τ4 ⟩)
    Eq0FailedCast : ∀{d1 d2 τ1 τ2 τ3 τ4} → d1 =0 d2 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0 (d2 ⟨ τ3 ⇒⦇-⦈⇏ τ4 ⟩)

  data _=0'_ : (d1 d2 : ihexp) → Set where 
    Eq0Const : c =0' c
    Eq0Var : ∀{x} → (X x) =0' (X x) 
    Eq0EHole : ⦇-⦈ =0' ⦇-⦈
    Eq0Lam : ∀{d1 d2 τ1 τ2} → d1 =0' d2 → (·λ[ τ1 ] d1) =0' (·λ[ τ2 ] d2)
    Eq0TLam : ∀{d1 d2} → d1 =0' d2 → (·Λ d1) =0' (·Λ d2)
    Eq0NEHole : ∀{d1 d2} → d1 =0' d2 →  ⦇⌜ d1 ⌟⦈ =0' ⦇⌜ d2 ⌟⦈
    Eq0Ap :  ∀{d1 d2 d3 d4} → d1 =0' d3 →  d2 =0' d4 →  (d1 ∘ d2) =0' (d3 ∘ d4)
    Eq0TAp : ∀{d1 d2 τ1 τ2} → d1 =0' d2 → (d1 < τ1 >) =0' (d2 < τ2 >)
    Eq0Cast : ∀{d1 d2 τ1 τ2} → d1 =0' d2 → (d1 ⟨ τ1 ⇒ τ1 ⟩) =0' (d2 ⟨ τ2 ⇒ τ2 ⟩)
    Eq0FailedCast : ∀{d1 d2 τ1 τ2} → d1 =0' d2 → (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0' (d2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  data _=0e_ : (e1 e2 : hexp) → Set where
    Eq0Const : c =0e c
    Eq0Var : ∀{x} → (X x) =0e (X x) 
    Eq0Asc : ∀{e1 e2 τ1 τ2} → e1 =0e e2 → (e1 ·: τ1) =0e (e2 ·: τ2)
    Eq0EHole : ⦇-⦈ =0e ⦇-⦈
    Eq0ULam : ∀{e1 e2} → e1 =0e e2 → (·λ e1) =0e (·λ e2)
    Eq0Lam : ∀{e1 e2 τ1 τ2} → e1 =0e e2 → (·λ[ τ1 ] e1) =0e (·λ[ τ2 ] e2)
    Eq0TLam : ∀{e1 e2} → e1 =0e e2 → (·Λ e1) =0e (·Λ e2)
    Eq0NEHole : ∀{e1 e2} → e1 =0e e2 →  (⦇⌜ e1 ⌟⦈) =0e (⦇⌜ e2 ⌟⦈)
    Eq0Ap :  ∀{e1 e2 e3 e4} → e1 =0e e3 →  e2 =0e e4 →  (e1 ∘ e2) =0e (e3 ∘ e4)
    Eq0TAp : ∀{e1 e2 τ1 τ2} → e1 =0e e2 → (e1 < τ1 >) =0e (e2 < τ2 >)

  data _=0ε'_ : (ε1 ε2 : ectx) → Set where 
    Eq0Dot : ⊙ =0ε' ⊙
    Eq0Ap1 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε' ε2) → (d1 =0' d2) → (ε1 ∘₁ d1) =0ε' (ε2 ∘₁ d2)
    Eq0Ap2 : ∀{ε1 ε2 d1 d2} → (ε1 =0ε' ε2) → (d1 =0' d2) → (d1 ∘₂ ε1) =0ε' (d2 ∘₂ ε2)
    Eq0TAp : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε' ε2) → (ε1 < τ1 >) =0ε' (ε2 < τ2 >)
    Eq0NEHole : ∀{ε1 ε2} → (ε1 =0ε' ε2) → ⦇⌜ ε1 ⌟⦈ =0ε' ⦇⌜ ε2 ⌟⦈
    Eq0Cast : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε' ε2) → (ε1 ⟨ τ1 ⇒ τ1 ⟩) =0ε' (ε2 ⟨ τ2 ⇒ τ2 ⟩)
    Eq0FailedCast : ∀{ε1 ε2 τ1 τ2} → (ε1 =0ε' ε2) → (ε1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) =0ε' (ε2 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  eq0-refl : ∀{d : ihexp} → d =0 d
  eq0-refl {d = c} = Eq0Const
  eq0-refl {d = X x} = Eq0Var
  eq0-refl {d = ·λ[ x₁ ] d} = Eq0Lam eq0-refl
  eq0-refl {d = ·Λ d} = Eq0TLam eq0-refl
  eq0-refl {d = ⦇-⦈} = Eq0EHole
  eq0-refl {d = ⦇⌜ d ⌟⦈} = Eq0NEHole eq0-refl
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

  eq0-boxedval' : 
    ∀ {d1 d2} →
    d1 =0' d2 →
    d1 boxedval →
    d2 boxedval
  eq0-boxedval' {d2 = d2} Eq0Const bv = bv
  eq0-boxedval' {d2 = d2} Eq0Var bv = bv
  eq0-boxedval' {d2 = d2} (Eq0Lam eq) bv = BVVal VLam
  eq0-boxedval' {d2 = d2} (Eq0TLam eq) bv = BVVal VTLam
  eq0-boxedval' (Eq0Cast eq) (BVArrCast x bv) = abort (x refl)
  eq0-boxedval' (Eq0Cast eq) (BVForallCast x bv) = abort (x refl)
  eq0-boxedval' (Eq0Cast eq) (BVHoleCast () bv)
  eq0-boxedval' Eq0EHole (BVVal ())
  eq0-boxedval' (Eq0NEHole eq) (BVVal ())
  eq0-boxedval' (Eq0Ap eq eq₁) (BVVal ())
  eq0-boxedval' (Eq0TAp eq) (BVVal ())
  eq0-boxedval' (Eq0FailedCast x₁) (BVVal ())

  eq0-↑d : ∀{t1 n t2 m d d'} → d =0' d' → ↑d t1 n t2 m d =0' ↑d t1 n t2 m d'
  eq0-↑d Eq0Const = Eq0Const
  eq0-↑d Eq0Var = Eq0Var
  eq0-↑d Eq0EHole = Eq0EHole
  eq0-↑d (Eq0Lam eq) = Eq0Lam (eq0-↑d eq)
  eq0-↑d (Eq0TLam eq) = Eq0TLam (eq0-↑d eq)
  eq0-↑d (Eq0NEHole eq) = Eq0NEHole (eq0-↑d eq)
  eq0-↑d (Eq0Ap eq eq₁) = Eq0Ap (eq0-↑d eq) (eq0-↑d eq₁)
  eq0-↑d (Eq0TAp eq) = Eq0TAp (eq0-↑d eq)
  eq0-↑d (Eq0Cast eq) = Eq0Cast (eq0-↑d eq)
  eq0-↑d (Eq0FailedCast eq) = Eq0FailedCast (eq0-↑d eq)

  eq0-ttSub : ∀{n m d1 d2 d1' d2'} → d1 =0' d1' → d2 =0' d2' → ttSub n m d1 d2 =0' ttSub n m d1' d2'
  eq0-ttSub eq1 Eq0Const = Eq0Const
  eq0-ttSub eq1 Eq0EHole = Eq0EHole
  eq0-ttSub eq1 (Eq0NEHole eq2) = Eq0NEHole (eq0-ttSub eq1 eq2)
  eq0-ttSub eq1 (Eq0Ap eq2 eq3) = Eq0Ap (eq0-ttSub eq1 eq2) (eq0-ttSub eq1 eq3)
  eq0-ttSub eq1 (Eq0TAp eq2) = Eq0TAp (eq0-ttSub eq1 eq2)
  eq0-ttSub eq1 (Eq0Cast eq2) = Eq0Cast (eq0-ttSub eq1 eq2)
  eq0-ttSub eq1 (Eq0FailedCast eq2) = Eq0FailedCast (eq0-ttSub eq1 eq2)
  eq0-ttSub {n} {m} {d1} {d1'} {d2} {d2'} eq1 (Eq0Lam {d3} {d4} {τ1} {τ2} eq2) = Eq0Lam (eq0-ttSub eq1 eq2)
  eq0-ttSub {n} {m} {d1} {d2} {d1'} {d2'} eq1 (Eq0TLam {d3} {d4} eq2) = Eq0TLam (eq0-ttSub eq1 eq2)
  eq0-ttSub {n} {m} {d1} {_} {d1'} eq1 (Eq0Var {x = x}) with natEQ x n 
  ... | Inl refl = eq0-↑d eq1  
  ... | Inr neq = Eq0Var

  eq0-TtSub : ∀{n τ1 τ2 d1 d2} → d1 dcompleteid → d1 =0' d2 → TtSub n τ1 d1 =0' TtSub n τ2 d2
  eq0-TtSub dc Eq0Const = Eq0Const
  eq0-TtSub dc Eq0Var = Eq0Var
  eq0-TtSub dc Eq0EHole = Eq0EHole
  eq0-TtSub (DCLam dc x) (Eq0Lam eq) = Eq0Lam (eq0-TtSub dc eq) 
  eq0-TtSub {n} {τ1} {τ2} (DCTLam dc) (Eq0TLam {d1 = d1} {d2 = d2} eq) = Eq0TLam (eq0-TtSub dc eq)
  eq0-TtSub () (Eq0NEHole eq)
  eq0-TtSub (DCAp dc dc₁) (Eq0Ap eq eq₁) = Eq0Ap (eq0-TtSub dc eq) (eq0-TtSub dc₁ eq₁) 
  eq0-TtSub (DCTAp x dc) (Eq0TAp eq) = Eq0TAp (eq0-TtSub dc eq) 
  eq0-TtSub (DCCast dc x) (Eq0Cast eq) = Eq0Cast (eq0-TtSub dc eq) 
  eq0-TtSub () (Eq0FailedCast eq)

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
  eq0'-eq0 (Eq0Cast eq0) = Eq0Cast (eq0'-eq0 eq0)
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
  eq0-eq0' (DCCast complete t1compl) (DCCast complete' t1compl') (Eq0Cast eq0) = Eq0Cast (eq0-eq0' complete complete' eq0)

  mutual
    eq0-elab-syn : ∀{e e' Γ Γ' d1 d2 τ τ'} →
      e =0e e' →
      Γ ⊢ e ⇒ τ ~> d1 →
      Γ' ⊢ e' ⇒ τ' ~> d2 →
      d1 =0 d2
    eq0-elab-syn Eq0Const ESConst ESConst = Eq0Const
    eq0-elab-syn Eq0Var (ESVar x) (ESVar x₁) = Eq0Var
    eq0-elab-syn (Eq0Asc eq0) (ESAsc x x₁) (ESAsc x₂ x₃) = Eq0Cast (eq0-elab-ana eq0 x₁ x₃)
    eq0-elab-syn Eq0EHole ESEHole ESEHole = Eq0EHole
    eq0-elab-syn (Eq0Lam eq0) (ESLam x elab1) (ESLam x₂ elab2) = Eq0Lam (eq0-elab-syn eq0 elab1 elab2)
    eq0-elab-syn (Eq0TLam eq0) (ESTLam _ _ elab1) (ESTLam _ _ elab2) = Eq0TLam (eq0-elab-syn eq0 elab1 elab2)
    eq0-elab-syn (Eq0NEHole eq0) (ESNEHole elab1) (ESNEHole elab2) = Eq0NEHole (eq0-elab-syn eq0 elab1 elab2)
    eq0-elab-syn (Eq0Ap eq0 eq1) (ESAp x x₁ x₂ x₄) (ESAp x₆ x₇ x₈ x₁₀) = Eq0Ap (Eq0Cast (eq0-elab-ana eq0 x₂ x₈)) (Eq0Cast (eq0-elab-ana eq1 x₄ x₁₀))
    eq0-elab-syn (Eq0TAp eq0) (ESTAp x x₁ x₂ x₃ x₄) (ESTAp x₅ x₆ x₇ x₈ x₉) = Eq0TAp (Eq0Cast (eq0-elab-ana eq0 x₃ x₈))

    eq0-elab-ana : ∀{e e' Γ Γ' d1 d2 τ1 τ1' τ2 τ2''} →
      e =0e e' →
      Γ ⊢ e ⇐ τ1 ~> d1 :: τ1' →
      Γ' ⊢ e' ⇐ τ2 ~> d2 :: τ2'' →
      d1 =0 d2
    eq0-elab-ana (Eq0ULam eq0) (EALam x elab1) (EALam x₂ elab2) = Eq0Lam (eq0-elab-ana eq0 elab1 elab2)
    eq0-elab-ana (Eq0TLam eq0) (EATLam x₂ elab1) (EATLam x₅ elab2) = Eq0TLam (eq0-elab-ana eq0 elab1 elab2)
    eq0-elab-ana eq0 (EASubsume x x₂ x₃) (EASubsume x₅ x₆ x₇) = Eq0Cast (eq0-elab-syn eq0 x₂ x₆)
    eq0-elab-ana (Eq0TLam eq0) (EASubsume (Subsumable _ _ neq) x₂ x₃) (EATLam x₇ ana) = abort (neq _ refl)
    eq0-elab-ana (Eq0TLam eq0) (EATLam x₅ ana) (EASubsume (Subsumable _ _ neq) x₂ x₃) = abort (neq _ refl)

  consist-complete-eq : ∀{τ τ'} →
    τ tcomplete →
    τ' tcomplete →
    τ ~ τ' →
    τ == τ'
  consist-complete-eq TCBase TCBase ConsistBase = refl
  consist-complete-eq TCVar TCVar ConsistVar = refl
  consist-complete-eq (TCArr tc1 tc2) (TCArr tc3 tc4) (ConsistArr con con₁) rewrite consist-complete-eq tc1 tc3 con rewrite consist-complete-eq tc2 tc4 con₁ = refl
  consist-complete-eq (TCForall tc1) (TCForall tc2) (ConsistForall con) rewrite consist-complete-eq tc1 tc2 con = refl
  
  compl-wt-complid : ∀{d Γ τ} →
    d dcomplete →
    Γ ⊢ d :: τ →
    d dcompleteid
  compl-wt-complid DCVar (TAVar x) = DCVar
  compl-wt-complid DCConst TAConst = DCConst
  compl-wt-complid (DCLam compl x) (TALam x₁ wt) = DCLam (compl-wt-complid compl wt) x
  compl-wt-complid (DCTLam compl) (TATLam wt) = DCTLam (compl-wt-complid compl wt)
  compl-wt-complid (DCAp compl compl₁) (TAAp wt wt₁) = DCAp (compl-wt-complid compl wt) (compl-wt-complid compl₁ wt₁)
  compl-wt-complid (DCTAp x compl) (TATAp x₁ wt x₂) = DCTAp x (compl-wt-complid compl wt)
  compl-wt-complid (DCCast compl x x₁) (TACast wt x₂ x₃) rewrite consist-complete-eq x x₁ x₃ = DCCast (compl-wt-complid compl wt) x₁

  complid-compl : ∀{d} →
    d dcompleteid →
    d dcomplete
  complid-compl DCVar = DCVar
  complid-compl DCConst = DCConst
  complid-compl (DCLam compl x) = DCLam (complid-compl compl) x
  complid-compl (DCTLam compl) = DCTLam (complid-compl compl)
  complid-compl (DCAp compl compl₁) = DCAp (complid-compl compl) (complid-compl compl₁)
  complid-compl (DCTAp x compl) = DCTAp x (complid-compl compl)
  complid-compl (DCCast compl x) = DCCast (complid-compl compl) x x

  dcompleteid-elab : ∀{e τ d} →
            e ecomplete →
            ∅ ⊢ e ⇒ τ ~> d →
            d dcompleteid
  dcompleteid-elab ec elab with complete-elaboration-synth GCEmpty ec elab | typed-elaboration-syn CtxWFEmpty elab
  ... | (dc , tc) | wt = compl-wt-complid dc wt
  
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
  eq0-ctxin' (Eq0Cast eq) (FHCast ctxin) with eq0-ctxin' eq ctxin 
  ... | d2' , ε2 , eq1 , eq2 , eq3 = _ , _ , FHCast eq1 , eq2 , Eq0Cast eq3
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
  eq0-ctxout' eq1 (Eq0Cast eq2) (FHCast eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHCast eq4 , Eq0Cast eq5
  eq0-ctxout' eq1 (Eq0FailedCast eq2) (FHFailedCast eq3) with eq0-ctxout' eq1 eq2 eq3 
  ... | _ , eq4 , eq5 = _ , FHFailedCast eq4 , Eq0FailedCast eq5

  eq0-instep' : 
    ∀ {d1 d2 d1' τ τ'} →
    d1 =0' d2 →
    d1 →> d1' →
    d1 dcompleteid →
    ∅ ⊢ d1 :: τ →
    ∅ ⊢ d2 :: τ' →
    Σ[ d2' ∈ ihexp ] ((d2 →> d2') × (d1' =0' d2'))
  eq0-instep' {d1 = (·λ[ τ1 ] d1) ∘ d1'} {d2 = (·λ[ τ2 ] d2) ∘ d2'} (Eq0Ap (Eq0Lam eq0) eq1) ITLam compl wt1 wt2 = _ , ITLam , eq0-ttSub eq1 eq0
  eq0-instep' {d1 = (d1' ⟨ τ1 ==> τ3 ⇒ τ1' ==> τ3' ⟩) ∘ d5} {d2 = (d2' ⟨ τ2 ==> τ ⇒ τ2' ==> τ' ⟩) ∘ d4}
    (Eq0Ap (Eq0Cast eq0) eq1) ITApCast compl wt1 (TAAp (TACast wt x₁ x₂) wt₁) = 
      ((d2' ∘ (d4 ⟨ τ2' ⇒ τ2 ⟩)) ⟨ τ ⇒ τ' ⟩) , ITApCast , Eq0Cast (Eq0Ap eq0 (Eq0Cast eq1))
  eq0-instep' {d1 = ·Λ d1 < _ >} {d2 = ·Λ d2 < τ2 >} (Eq0TAp (Eq0TLam eq0)) ITTLam (DCTAp x (DCTLam compl)) (TATAp x₁ (TATLam wt1) x₂) (TATAp x₃ (TATLam wt2) x₄) = _ , ITTLam , eq0-TtSub compl eq0 
  eq0-instep' {d1 = (d1 ⟨ ·∀ τ ⇒ ·∀ τ' ⟩) < τ1 >} {d2 = (d2 ⟨ ·∀ τ2 ⇒ ·∀ τ2' ⟩) < τ3 >} 
    (Eq0TAp (Eq0Cast eq0)) ITTApCast compl (TATAp x₅ (TACast wt1 x₇ x₈) x₆) (TATAp x (TACast wt x₂ x₃) x₁) = _ , ITTApCast , Eq0Cast (Eq0TAp eq0)
  eq0-instep' {d2 = d2 ⟨ τ2 ⇒ τ2' ⟩} (Eq0Cast eq0) ITCastID compl wt1 wt = d2 , ITCastID , eq0
  eq0-instep' (Eq0Cast x₂) (ITCastSucceed x₅) (DCCast x ()) wt1 x₁
  eq0-instep' (Eq0Cast x₂) (ITCastFail _ _ x₅) (DCCast x ()) wt1 x₁
  eq0-instep' (Eq0Cast x₂) (ITGround x₅) (DCCast x ()) wt1 x₁
  eq0-instep' (Eq0Cast x₂) (ITExpand x₅) (DCCast x ()) wt1 x₁

  completeid-env : ∀{d d' ε} →
    d' dcompleteid →
    d' == ε ⟦ d ⟧ →
    d dcompleteid
  completeid-env dc FHOuter = dc
  completeid-env (DCAp dc dc₁) (FHAp1 env) = completeid-env dc env
  completeid-env (DCAp dc dc₁) (FHAp2 env) = completeid-env dc₁ env
  completeid-env (DCTAp x dc) (FHTAp env) = completeid-env dc env
  completeid-env (DCCast dc x) (FHCast env) = completeid-env dc env

  wt-env : ∀{d d' ε τ} →
    ∅ ⊢ d :: τ →
    d == ε ⟦ d' ⟧ →
    Σ[ τ' ∈ htyp ] (∅ ⊢ d' :: τ')
  wt-env {τ = τ} wt FHOuter = τ , wt
  wt-env {τ = τ} (TAAp {τ1 = τ1} wt wt₁) (FHAp1 env₁) = wt-env wt env₁
  wt-env {τ = τ} (TAAp wt wt₁) (FHAp2 env₁) = wt-env wt₁ env₁
  wt-env {τ = τ} (TATAp x wt x₁) (FHTAp env₁) = wt-env wt env₁
  wt-env {τ = τ} (TANEHole wt) (FHNEHole env₁) = wt-env wt env₁
  wt-env {τ = τ} (TACast wt x x₁) (FHCast env₁) = wt-env wt env₁
  wt-env {τ = τ} (TAFailedCast wt x x₁ x₂) (FHFailedCast env₁) = wt-env wt env₁

  eq0-step' : 
    ∀ {d1 d2 d1' τ τ'} →
    d1 dcompleteid →
    ∅ ⊢ d1 :: τ →
    ∅ ⊢ d2 :: τ' →
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

  compl-complid-pres : ∀{d d' τ} →
    d dcompleteid → 
    ∅ ⊢ d :: τ → 
    d ↦ d' →
    d' dcompleteid
  compl-complid-pres compl wt step = compl-wt-complid (complete-preservation (complid-compl compl) wt step) (preservation wt step) 

  parametricity11_rec : 
    ∀ {τ τ' d1 d2 v1 } →
    d1 dcompleteid →
    d2 dcompleteid →
    ∅ ⊢ d1 :: τ → 
    ∅ ⊢ d2 :: τ' → 
    d1 =0' d2 →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ] ((d2 ↦* v2) × (v2 boxedval) × (v1 =0' v2))
  parametricity11_rec c1 c2 wt1 wt2 eq0 MSRefl bv = _ , MSRefl , eq0-boxedval' eq0 bv , eq0
  parametricity11_rec c1 c2 wt1 wt2 eq0 (MSStep x step) bv
    with eq0-step' c1 wt1 wt2 eq0 x
  ... | ( d2' , step2 , eq2 )
    with complete-preservation (complid-compl c1) wt1 x | complete-preservation (complid-compl c2) wt2 step2 | preservation wt1 x | preservation wt2 step2
  ... | c1' | c2' | wt1' | wt2'
    with parametricity11_rec (compl-wt-complid c1' wt1') (compl-wt-complid c2' wt2') wt1' wt2' eq2 step bv
  ... | ( v2 , steps2 , bv2 , eq3 ) = v2 , MSStep step2 steps2  , bv2 , eq3
 
  parametricity11 : 
    ∀ {e e' τ τ' d1 d2 v1 } →
    e ecomplete →
    e' ecomplete →
    e =0e e' →
    ∅ ⊢ e ⇒ τ ~> d1 →     
    ∅ ⊢ e' ⇒ τ' ~> d2 →
    d1 ↦* v1 →
    v1 boxedval →
    Σ[ v2 ∈ ihexp ] ((d2 ↦* v2) × (v2 boxedval) × (v1 =0 v2))
  parametricity11 ec ec' eeq elab1 elab2 eval bv =
    let d1c = (dcompleteid-elab ec elab1) in
    let d2c = (dcompleteid-elab ec' elab2) in
    let (v2 , v2eval , v2bv , eq0') = parametricity11_rec d1c d2c (typed-elaboration-syn CtxWFEmpty elab1) (typed-elaboration-syn CtxWFEmpty elab2) (eq0-eq0' d1c d2c (eq0-elab-syn eeq elab1 elab2)) eval bv in
    (v2 , v2eval , v2bv , eq0'-eq0 eq0')     