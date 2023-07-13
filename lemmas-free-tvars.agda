open import Prelude
open import core
open import Nat

module lemmas-free-tvars where

  open typctx

  
  wf-no-subst : ∀{t n y} -> ~∅ ⊢ y wf -> y == (Typ[ t / n ] y)
  wf-no-subst (WFVar ())
  wf-no-subst WFBase = refl
  wf-no-subst WFHole = refl
  wf-no-subst {t} {n} {y} (WFArr {gamma} {dom} {cod} xwf ywf) with wf-no-subst {t} {n} xwf | wf-no-subst {t} {n} ywf
  ... | refl | bb = {!!}
  
  -- let dom' = wf-no-subst {t} {n} xwf in let cod' = wf-no-subst {t} {n} ywf in {! !}
  wf-no-subst (WFForall p) = {!!}
