open import Prelude
open import core
open import Nat
open import contexts

module lemmas-free-tvars where

  open typctx

  nftv-no-subst : ∀{t n y o} -> o ⊢ y wf -> ((n < typctx.n o) -> ⊥) -> y == (Typ[ t / n ] y)
  nftv-no-subst {n = n} {y = T a} {o = o} (WFVar l) lte with natEQ n a
  ... | Inl refl = abort (lte l) 
  ... | Inr neq with natLT n a
  ... | Inl (LTZ) = abort (lte (let p1 , p2 = lt-gtz {typctx.n o} l in foo p2))
    where
      foo : {n m : Nat} -> n == 1+ m -> Z < n
      foo p rewrite p = LTZ
  ... | Inl (LTS p) = let temp = lt-trans (LTS p) l in abort (lte temp)
  ... | Inr _ = refl
  nftv-no-subst WFBase _ = refl
  nftv-no-subst WFHole _ = refl
  nftv-no-subst (WFArr {gamma} {dom} {cod} xwf ywf) p = foo (nftv-no-subst xwf p) (nftv-no-subst ywf p)
    where
      foo : ∀{A B C D} -> A == C -> B == D -> (A ==> B) == (C ==> D)
      foo A==C B==D rewrite A==C rewrite B==D = refl
  nftv-no-subst {n = n} (WFForall p) pf = foo (nftv-no-subst p (\{(LTS pf') -> pf pf'}))
    where
      foo : ∀{A B} -> A == B -> ·∀ A == ·∀ B
      foo eq rewrite eq = refl
  
  wf-no-subst : ∀{t n y} -> ~∅ ⊢ y wf -> y == (Typ[ t / n ] y)
  wf-no-subst {n = n} p = nftv-no-subst p (\ ()) 

  empty-tctx-closed : ∀{o} -> o ⊢ ∅ tctxwf
  empty-tctx-closed = CCtx (λ ())

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

  lemma-subst-apart : ∀{x Γ t n} -> x # Γ -> x # (Tctx[ t / n ] Γ)
  lemma-subst-apart {x = x} {Γ = Γ} p with Γ x 
  ... | None = refl
  ... | Some t = abort (foo p)
    where
      foo : ∀{x} -> Some x == None -> ⊥
      foo = \ ()

  lemma-union-subst-comm :  ∀{Γ1 Γ2 : tctx} {t : htyp} {n : Nat} -> (Tctx[ t / n ] Γ1) ∪ (Tctx[ t / n ] Γ2) == Tctx[ t / n ] (Γ1 ∪ Γ2)
  lemma-union-subst-comm {Γ1} {Γ2} {t} {n} = funext (\x -> helper x)
    where
      helper : (x : Nat) -> ((Tctx[ t / n ] Γ1) ∪ (Tctx[ t / n ] Γ2)) x == (Tctx[ t / n ] (Γ1 ∪ Γ2)) x
      helper x with ctxindirect (Tctx[ t / n ] Γ1) x | ctxindirect Γ1 x
      ... | Inl (_ , ingamma1l) | Inl (_ , ingamma1r) rewrite ingamma1l rewrite ingamma1r = !(ingamma1l)
      ... | Inl (_ , ingamma1l) | Inr notingamma1r rewrite ingamma1l rewrite notingamma1r = abort (somenotnone (!(ingamma1l)))
      ... | Inr notingamma1l | Inl (_ , ingamma1r) rewrite notingamma1l rewrite ingamma1r = abort (somenotnone notingamma1l)
      ... | Inr notingamma1l | Inr notingamma1r rewrite notingamma1l rewrite notingamma1r with ctxindirect (Tctx[ t / n ] Γ2) x | ctxindirect Γ2 x
      ...   | Inl (_ , ingamma2l) | Inl (_ , ingamma2r) rewrite ingamma2l rewrite ingamma2r = !(ingamma2l)
      ...   | Inr notingamma2l | Inr notingamma2r rewrite notingamma2l rewrite notingamma2r = refl
      ...   | Inl (_ , ingamma2l) | Inr notingamma2r rewrite ingamma2l rewrite notingamma2r = abort (somenotnone (!(ingamma2l)))
      ...   | Inr notingamma2l | Inl (_ , ingamma2r) rewrite notingamma2l rewrite ingamma2r = abort (somenotnone notingamma2l)

  subst-singleton : ∀{x : Nat} {Γ : tctx} {t : htyp} {n : Nat} {τ : htyp} -> (■ (x , Typ[ t / n ] τ)) == Tctx[ t / n ] (■ (x , τ))
  subst-singleton {x} {Γ} {t} {n} {τ} = funext (\y -> helper y)
    where
      helper : (y : Nat) -> (■ (x , Typ[ t / n ] τ)) y == (Tctx[ t / n ] (■ (x , τ))) y
      helper y with natEQ x y
      ... | Inl refl = refl
      ... | Inr neq = refl

  lemma-extend-subst-comm : ∀{Γ x τ t n} -> (Tctx[ t / n ] Γ) ,, (x , Typ[ t / n ] τ) == (Tctx[ t / n ] (Γ ,, (x , τ)))
  lemma-extend-subst-comm {Γ} {x} {τ} {t} {n} rewrite subst-singleton {x} {Γ} {t} {n} {τ} = lemma-union-subst-comm {Γ} {■ (x , τ)} {t} {n}
