open import Nat
open import Prelude
open import List
open import core

module expansion-unicity where
  mutual
    expansion-unicity-synth : (Γ : ·ctx) (e : ė) (t1 t2 : τ̇) (e1' e2' : ë) (Δ1 Δ2 : ·ctx) →
                            Γ ⊢ e ⇒ t1 ~> e1' ⊣ Δ1 →
                            Γ ⊢ e ⇒ t2 ~> e2' ⊣ Δ2 →
                            t1 == t2 × e1' == e2' × Δ1 == Δ2
    expansion-unicity-synth = {!!}

    expansion-unicity-ana : (Γ : ·ctx) (e : ė) (t1 t1' t2 t2' : τ̇) (e1' e2' : ë) (Δ1 Δ2 : ·ctx) →
                          Γ ⊢ e ⇐ t1 ~> e1' :: t1' ⊣ Δ1 →
                          Γ ⊢ e ⇐ t2 ~> e2' :: t2' ⊣ Δ2 →
                          t1 == t2 × e1' == e2' × t1' == t2' × Δ1 == Δ2
    expansion-unicity-ana = {!!}
