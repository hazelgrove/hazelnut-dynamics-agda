open import Nat
open import Prelude
open import List
open import core

module expansion-unicity where
  mutual
    expansion-unicity-synth : (Γ : tctx) (e : hexp) (t1 t2 : htyp) (d1 d2 : dhexp) (Δ1 Δ2 : hctx) →
                            Γ ⊢ e ⇒ t1 ~> d1 ⊣ Δ1 →
                            Γ ⊢ e ⇒ t2 ~> d2 ⊣ Δ2 →
                            t1 == t2 × d1 == d2 × Δ1 == Δ2
    expansion-unicity-synth = {!!}

    expansion-unicity-ana : (Γ : tctx) (e : hexp) (t1 t1' t2 t2' : htyp) (d1 d2 : dhexp) (Δ1 Δ2 : hctx) →
                          Γ ⊢ e ⇐ t1 ~> d1 :: t1' ⊣ Δ1 →
                          Γ ⊢ e ⇐ t2 ~> d2 :: t2' ⊣ Δ2 →
                          t1 == t2 × d1 == d2 × t1' == t2' × Δ1 == Δ2
    expansion-unicity-ana = {!!}
