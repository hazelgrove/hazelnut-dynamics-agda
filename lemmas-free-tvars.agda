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

  empty-tctx-closed : closed-tctx ∅
  empty-tctx-closed = CCtx (λ ())
