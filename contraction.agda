open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

module contraction where
  -- in the same style as the proofs of exchange, this argument along with
  -- trasnport allows you to prove contraction for all the hypothetical
  -- judgements uniformly. we never explicitly use contraction anywhere, so
  -- we omit any of the specific instances for concision; they are entirely
  -- mechanical, as are the specific instances of exchange. one is shown
  -- below as an example.
  contract : {A : Set} {x : Nat} {τ : A} (Γ : A ctx) →
         ((Γ ,, (x , τ)) ,, (x , τ)) == (Γ ,, (x , τ))
  contract {A} {x} {τ} Γ = funext guts
    where
      guts : (y : Nat) → (Γ ,, (x , τ) ,, (x , τ)) y == (Γ ,, (x , τ)) y
      guts y with natEQ x y
      guts .x | Inl refl with Γ x
      guts .x | Inl refl | Some x₁ = refl
      guts .x | Inl refl | None with natEQ x x
      guts .x | Inl refl | None | Inl refl = refl
      guts .x | Inl refl | None | Inr x₁ = abort (x₁ refl)
      guts y | Inr x₁ with Γ y
      guts y | Inr x₂ | Some x₁ = refl
      guts y | Inr x₁ | None with natEQ x y
      guts .x | Inr x₂ | None | Inl refl = refl
      guts y | Inr x₂ | None | Inr x₁ with natEQ x y
      guts .x | Inr x₃ | None | Inr x₂ | Inl refl = abort (x₃ refl)
      guts y | Inr x₃ | None | Inr x₂ | Inr x₁ = refl

  contract-synth : ∀{ Γ x τ e τ'}
                  → (Γ ,, (x , τ) ,, (x , τ)) ⊢ e => τ'
                  → (Γ ,, (x , τ)) ⊢ e => τ'
  contract-synth {Γ = Γ} {e = e} {τ' = τ'} =
    tr (λ qq → qq ⊢ e => τ') (contract Γ)

  -- as an aside, this also establishes the other direction which is rarely
  -- mentioned, since equality is symmetric
  expand-synth : ∀{ Γ x τ e τ'}
                  → (Γ ,, (x , τ)) ⊢ e => τ'
                  → (Γ ,, (x , τ) ,, (x , τ)) ⊢ e => τ'
  expand-synth {Γ = Γ} {e = e} {τ' = τ'} =
    tr (λ qq → qq ⊢ e => τ') (! (contract Γ))
