open import Prelude
open import core
open import contexts

module synth-unicity where
  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic positions because we think of
  -- the type as an input
  synthunicity : {Γ : tctx} {e : ė} {t t' : τ̇} →
                  (Γ ⊢ e => t)
                → (Γ ⊢ e => t')
                → t == t'
  synthunicity (SAsc _) (SAsc _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp D1 MAHole b) (SAp D2 MAHole y) = refl
  synthunicity (SAp D1 MAHole b) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr b) (SAp D2 MAHole y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr b) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | refl = refl
  synthunicity SNum SNum = refl
  synthunicity (SPlus _ _ ) (SPlus _ _ ) = refl
  synthunicity SEHole SEHole = refl
  synthunicity (SNEHole _) (SNEHole _) = refl
