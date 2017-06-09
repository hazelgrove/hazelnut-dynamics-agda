open import Nat
open import Prelude
open import List
open import core

module correspondence where
  mutual
    correspondence-synth : (Γ : tctx) (e : hexp) (t : htyp) (d : dhexp) (Δ : hctx) →
                            Γ ⊢ e ⇒ t ~> d ⊣ Δ →
                            Γ ⊢ e => t
    correspondence-synth = {!!}

    correspondence-ana : (Γ : tctx) (e : hexp) (t t' : htyp) (d : dhexp) (Δ : hctx)  →
                          Γ ⊢ e ⇐ t ~> d :: t' ⊣ Δ →
                          Γ ⊢ e => t
    correspondence-ana = {!!}
