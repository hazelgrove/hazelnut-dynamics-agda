open import Prelude
open import core
open import Nat

module lemmas-free-tvars where

  open typctx

  nftv-no-subst : ∀{t n y o} -> o ⊢ y wf -> typctx.n o < n + typctx.n o == n -> y == (Typ[ t / n ] y)
  nftv-no-subst {n = n} (WFForall p) pf = foo (nftv-no-subst p {!   !})
    where
      foo : ∀{A B} -> A == B -> ·∀ A == ·∀ B
      foo eq rewrite eq = refl
  nftv-no-subst _ _ = {!!}
  
  wf-no-subst : ∀{t n y} -> ~∅ ⊢ y wf -> y == (Typ[ t / n ] y)
  wf-no-subst {n = n} p with n 
  ... | Z = nftv-no-subst p (Inr refl) 
  ... | 1+ n = nftv-no-subst p (Inl LTZ) 
  {-
  wf-no-subst (WFVar ())
  wf-no-subst WFBase = refl
  wf-no-subst WFHole = refl
  wf-no-subst {t} {n} {y} (WFArr {gamma} {dom} {cod} xwf ywf) = foo (wf-no-subst xwf) (wf-no-subst ywf)
    where
      foo : ∀{A B C D} -> A == C -> B == D -> (A ==> B) == (C ==> D)
      foo A==C B==D rewrite A==C rewrite B==D = refl
  
  -- let dom' = wf-no-subst {t} {n} xwf in let cod' = wf-no-subst {t} {n} ywf in {! !}
  wf-no-subst {n = n} (WFForall p) with n 
  ... | Z = foo (nftv-no-subst p (Inr refl))
    where
      foo : ∀{A B} -> A == B -> ·∀ A == ·∀ B
      foo eq rewrite eq = refl
  ... | 1+ n' = foo (nftv-no-subst p (Inl (LTS LTZ)))
    where
      foo : ∀{A B} -> A == B -> ·∀ A == ·∀ B
      foo eq rewrite eq = refl
-}
  
  
