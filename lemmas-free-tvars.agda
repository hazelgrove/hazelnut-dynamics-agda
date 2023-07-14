open import Prelude
open import core
open import Nat

module lemmas-free-tvars where

  open typctx

  nftv-no-subst : ∀{t n y o} -> o ⊢ y wf -> ((n < typctx.n o) -> ⊥) -> y == (Typ[ t / n ] y)
  nftv-no-subst {n = n} {y = T a} {o = o} (WFVar l) lte with natEQ n a
--  ... | Inl refl | Inr eq = abort (lt-ne l (! eq)) 
--  ... | Inl refl | Inl lt = abort (lt-antisym l lt)
--  ... | Inr neq | Inr eq = {!!}
--  ... | Inr neq | Inl lt = {!!}
  ... | Inl refl = abort (lte l) 
  ... | Inr neq with natLT n a
  ... | Inl (LTZ) = abort (lte (let p1 , p2 = lt-gtz {typctx.n o} l in foo p2))
    where
      foo : {n m : Nat} -> n == 1+ m -> Z < n
      foo p rewrite p = LTZ
  ... | Inl (LTS p) = {!!}
  ... | Inr _ = refl

--  nftv-no-subst (WFVar ()) (Inl LTZ)
--  nftv-no-subst {n = n} {o = o} (WFVar l) (Inr refl) with l
--  ... | LTZ = refl
--  ... | LTS p = abort {! lt_ne {typctx.n o} {n} p !}
  nftv-no-subst WFBase _ = refl
  nftv-no-subst WFHole _ = refl
  nftv-no-subst {n = n} (WFForall p) pf = foo (nftv-no-subst p {!   !})
    where
      foo : ∀{A B} -> A == B -> ·∀ A == ·∀ B
      foo eq rewrite eq = refl
  nftv-no-subst _ _ = {!!}
  
  wf-no-subst : ∀{t n y} -> ~∅ ⊢ y wf -> y == (Typ[ t / n ] y)
  wf-no-subst {n = n} p with n 
  ... | Z = nftv-no-subst p {!!} -- (Inr refl) 
  ... | 1+ n = nftv-no-subst p {!!} -- (Inl LTZ) 
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
  
  
 