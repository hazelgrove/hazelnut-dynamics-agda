open import Nat
open import Prelude
open import List
open import core

module typed-expansion where
  mutual
    typed-expansion-synth : (Γ : tctx) (e : ė) (t : τ̇) (e' : ë) (Δ : hctx) →
                            Γ ⊢ e ⇒ t ~> e' ⊣ Δ →
                            Δ , Γ ⊢ e' :: t
    typed-expansion-synth = {!!}

    typed-expansion-ana : (Γ : tctx) (e : ė) (t : τ̇) (e' : ë) (Δ : hctx) (t' : τ̇) →
                          Γ ⊢ e ⇐ t ~> e' :: t' ⊣ Δ →
                          (t ~ t') × (Δ , Γ ⊢ e' :: t')
    typed-expansion-ana = {!!}
