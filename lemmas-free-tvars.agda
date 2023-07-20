open import Prelude
open import core
open import Nat
open import contexts

module lemmas-free-tvars where

  open typctx

  wf-no-subst : ∀{t n y o} -> o ⊢ y wf -> ((n < typctx.n o) -> ⊥) -> y == (Typ[ t / n ] y)
  wf-no-subst {n = n} {y = T a} {o = o} (WFVar l) lte with natEQ n a
  ... | Inl refl = abort (lte l) 
  ... | Inr neq with natLT n a
  ... | Inl (LTZ) = abort (lte (let p1 , p2 = lt-gtz {typctx.n o} l in foo p2))
    where
      foo : {n m : Nat} -> n == 1+ m -> Z < n
      foo p rewrite p = LTZ
  ... | Inl (LTS p) = let temp = lt-trans (LTS p) l in abort (lte temp)
  ... | Inr _ = refl
  wf-no-subst WFBase _ = refl
  wf-no-subst WFHole _ = refl
  wf-no-subst (WFArr {gamma} {dom} {cod} xwf ywf) p = foo (wf-no-subst xwf p) (wf-no-subst ywf p)
    where
      foo : ∀{A B C D} -> A == C -> B == D -> (A ==> B) == (C ==> D)
      foo A==C B==D rewrite A==C rewrite B==D = refl
  wf-no-subst {n = n} (WFForall p) pf = foo (wf-no-subst p (\{(LTS pf') -> pf pf'}))
    where
      foo : ∀{A B} -> A == B -> ·∀ A == ·∀ B
      foo eq rewrite eq = refl


  wf-tctx-no-subst : ∀ {o g t n} -> o ⊢ g tctxwf -> ((n < typctx.n o) -> ⊥) -> g == (Tctx[ t / n ] g)
  wf-tctx-no-subst {o} {g} {t} {n} (CCtx x) nbound = funext (\y -> helper y)
    where
      helper : (y : Nat) -> g y == (Tctx[ t / n ] g) y
      helper y with ctxindirect g y | ctxindirect (Tctx[ t / n ] g) y
      ... | Inl (_ , ing) | Inl (_ , ing') rewrite ing rewrite ing' rewrite wf-no-subst (x ing) nbound = ing'
      ... | Inr ning | Inr ning' = ning · ! ning'
      ... | Inl (_ , ing) | Inr ning' rewrite ing rewrite ning' = abort (somenotnone ning')
      ... | Inr ning | Inl (_ , ing') rewrite ning rewrite ing' = abort (somenotnone (! ing'))

  wf-weakening : ∀{t o} -> o ⊢ t wf -> [ o newtyp] ⊢ t wf
  wf-weakening (WFVar x) = WFVar (lt-right-incr x)
  wf-weakening WFBase = WFBase
  wf-weakening WFHole = WFHole
  wf-weakening (WFArr wf1 wf2) = WFArr (wf-weakening wf1) (wf-weakening wf2)
  wf-weakening (WFForall twf) = WFForall (wf-weakening twf)

  lemma-subst-tvar : ∀{t y n o} -> [ o newtyp] ⊢ y wf -> o ⊢ t wf -> n < 1+ (typctx.n o) -> o ⊢ (Typ[ t / n ] y) wf
  lemma-subst-tvar {y = b} _ _ _ = WFBase
  lemma-subst-tvar {y = T y} {n = n} (WFVar ywf) twf bnd with natEQ n y
  ... | Inl refl = twf
  ... | Inr neq with natLT n y
  ...   | Inl (LTZ {y'}) = WFVar (lt-1+-inj ywf)
  ...   | Inl (LTS p) = WFVar (lt-1+-inj ywf)
  ...   | Inr gte = let yltn = trichotomy-lemma neq gte in WFVar (lt-1+-inj (lt-trans-1+ yltn bnd))
  lemma-subst-tvar {y = ⦇-⦈} _ _ _ = WFHole
  lemma-subst-tvar {y = y ==> y₁} (WFArr wf1 wf2) twf bnd = WFArr (lemma-subst-tvar wf1 twf bnd) (lemma-subst-tvar wf2 twf bnd)
  lemma-subst-tvar {y = ·∀ y} (WFForall ywf) twf bnd = WFForall (lemma-subst-tvar ywf (wf-weakening twf) (LTS bnd))

  lemma-subst-outer : ∀{t y o} -> [ o newtyp] ⊢ y wf -> o ⊢ t wf -> o ⊢ (Typ[ t / Z ] y) wf
  lemma-subst-outer p q = lemma-subst-tvar p q LTZ

  lemma-subst-apart : ∀{Γ x t n} -> x # Γ -> x # (Tctx[ t / n ] Γ)
  lemma-subst-apart {Γ} {x} p with Γ x 
  ... | None = refl
  ... | Some t = abort (foo p)
    where
      foo : ∀{x} -> Some x == None -> ⊥
      foo = \ ()

  lemma-subst-elem : ∀{Γ x τ t n} -> (x , τ) ∈ Γ -> (x , Typ[ t / n ] τ) ∈ (Tctx[ t / n ] Γ)
  lemma-subst-elem {Γ} {x} {τ} {t} {n} p rewrite p = refl
