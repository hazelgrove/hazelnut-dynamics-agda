open import Prelude
open import Nat
open import core
open import contexts

module structural where
  postulate
       weaken-ana-expand : ∀{ Γ e τ e' τ' Δ x τ* } →
                        -- todo: there's a freshness concern here; i'm
                        -- not sure if just being apart from Γ is good
                        -- enough. in POPL work it wasn't, we wanted
                        -- really aggressive freshness because of
                        -- barendrecht's. we might be able to generate
                        -- that freshness from the first two premises.
                        x # Γ →
                        Γ ⊢ e ⇐ τ ~> e' :: τ' ⊣ Δ →
                        (Γ ,, (x , τ*)) ⊢ e ⇐ τ ~> e' :: τ' ⊣ Δ

  postulate
    lem-weakenΔ1 : ∀{Δ1 Δ2 Γ d τ} → Δ1 ## Δ2 → Δ1 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
