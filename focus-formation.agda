open import core

module focus-formation where
  -- every ε is an evaluation context -- trivially, here, since we don't
  -- include any of the premises in red brackets about finality
  focus-formation : ∀{d d' ε} → d == ε ⟦ d' ⟧ → ε evalctx
  focus-formation FHOuter = ECDot
  focus-formation (FHAp1 sub) = ECAp1 (focus-formation sub)
  focus-formation (FHAp2 sub) = ECAp2 (focus-formation sub)
  focus-formation (FHTAp sub) = ECTAp (focus-formation sub)
  focus-formation (FHNEHole sub) = ECNEHole (focus-formation sub)
  focus-formation (FHCast sub) = ECCast (focus-formation sub)
  focus-formation (FHFailedCast x) = ECFailedCast (focus-formation x)
