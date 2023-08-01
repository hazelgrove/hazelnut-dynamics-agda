open import Prelude
open import core
open import contexts

module synth-unicity where
  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic positions because we think of
  -- the type as an input
  synthunicity : ∀{Γ e t t' Θ} →
                  (Θ , Γ ⊢ e => t)
                → (Θ , Γ ⊢ e => t')
                → t == t'
  synthunicity (SAsc _ _) (SAsc _ _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp _  D1 MAHole _) (SAp _ D2 MAHole y) = refl
  synthunicity (SAp _ D1 MAHole _) (SAp _ D2 MAArr y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp _ D1 MAArr _) (SAp _ D2 MAHole y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp _ D1 MAArr _) (SAp _ D2 MAArr y) with synthunicity D1 D2
  ... | refl = refl
  synthunicity (STAp wf1 D1 MFHole eq1) (STAp wf2 D2 MFHole eq2) with synthunicity D1 D2 
  ... | refl rewrite (sym eq1) = eq2
  synthunicity (STAp wf1 D1 MFForall eq1) (STAp wf2 D2 MFHole eq2) with synthunicity D1 D2 
  ... | ()
  synthunicity (STAp wf1 D1 MFHole eq1) (STAp wf2 D2 MFForall eq2) with synthunicity D1 D2 
  ... | ()
  synthunicity (STAp wf1 D1 MFForall eq1) (STAp wf2 D2 MFForall eq2) with synthunicity D1 D2 
  ... | refl rewrite (sym eq1) = eq2 
  synthunicity SEHole SEHole = refl
  synthunicity (SNEHole _ _) (SNEHole _ _) = refl
  synthunicity SConst SConst = refl
  synthunicity (SLam _ _ D1) (SLam _ _ D2) with synthunicity D1 D2
  synthunicity (SLam wf1 x₁ D1) (SLam wf2 x₂ D2) | refl = refl
  synthunicity (STLam D1) (STLam D2) with synthunicity D1 D2 
  ... | refl = refl

