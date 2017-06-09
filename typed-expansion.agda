open import Nat
open import Prelude
open import List
open import core

module typed-expansion where
  mutual
    typed-expansion-synth : (Γ : tctx) (e : hexp) (t : htyp) (d : dhexp) (Δ : hctx) →
                            Γ ⊢ e ⇒ t ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: t
    typed-expansion-synth = {!!}

    typed-expansion-ana : (Γ : tctx) (e : hexp) (t t' : htyp) (d : dhexp) (Δ : hctx) →
                          Γ ⊢ e ⇐ t ~> d :: t' ⊣ Δ →
                          (t ~ t') × (Δ , Γ ⊢ d :: t')
    typed-expansion-ana = {!!}
