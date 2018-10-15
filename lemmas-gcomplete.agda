open import Prelude
open import Nat
open import core
open import contexts

module lemmas-gcomplete where
  -- if you add a complete type to a complete context, the result is also a
  -- complete context
  gcomp-extend : ∀{Γ τ x} → Γ gcomplete → τ tcomplete → x # Γ → (Γ ,, (x , τ)) gcomplete
  gcomp-extend {Γ} {τ} {x} gc tc apart x_query τ_query x₁ with natEQ x x_query
  gcomp-extend {Γ} {τ} {x} gc tc apart .x τ_query x₂ | Inl refl = tr (λ qq → qq tcomplete) (lem-apart-union-eq {Γ = Γ} apart x₂) tc
  gcomp-extend {Γ} {τ} {x} gc tc apart x_query τ_query x₂ | Inr x₁ = gc x_query τ_query (lem-neq-union-eq {Γ = Γ} (flip x₁) x₂ )
