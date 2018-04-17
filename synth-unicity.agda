open import Prelude
open import core
open import contexts

module synth-unicity where
  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic positions because we think of
  -- the type as an input
  synthunicity : {Γ : tctx} {e : hexp} {t t' : htyp} →
                  (Γ ⊢ e => t)
                → (Γ ⊢ e => t')
                → t == t'
  synthunicity (SAsc _) (SAsc _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp _  D1 MAHole _) (SAp _ D2 MAHole y) = refl
  synthunicity (SAp _ D1 MAHole _) (SAp _ D2 MAArr y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp _ D1 MAArr _) (SAp _ D2 MAHole y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp _ D1 MAArr _) (SAp _ D2 MAArr y) with synthunicity D1 D2
  ... | refl = refl
  synthunicity SEHole SEHole = refl
  synthunicity (SNEHole _ _) (SNEHole _ _) = refl
  synthunicity SConst SConst = refl
  synthunicity (SLam _ D1) (SLam _ D2) with synthunicity D1 D2
  synthunicity (SLam x₁ D1) (SLam x₂ D2) | refl = refl
