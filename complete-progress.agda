open import Nat
open import Prelude
open import List
open import core
open import contexts

open import progress
open import htype-decidable
open import lemmas-complete

module complete-progress where

  -- todo: explain this
  data okc : (d : ihexp) (Δ : hctx) → Set where
    V : ∀{d Δ} → d val → okc d Δ
    S : ∀{d Δ} → Σ[ d' ∈ ihexp ] (d ↦ d') → okc d Δ

  -- todo: lemma file if an arrow is disequal, it disagrees in the first or second argument
  ne-factor : ∀{τ1 τ2 τ3 τ4} → (τ1 ==> τ2) ≠ (τ3 ==> τ4) → (τ1 ≠ τ3) + (τ2 ≠ τ4)
  ne-factor {τ1} {τ2} {τ3} {τ4} ne with htype-dec τ1 τ3 | htype-dec τ2 τ4
  ne-factor ne | Inl refl | Inl refl = Inl (λ x → ne refl)
  ne-factor ne | Inl x | Inr x₁ = Inr x₁
  ne-factor ne | Inr x | Inl x₁ = Inl x
  ne-factor ne | Inr x | Inr x₁ = Inl x

  complete-progress : {Δ : hctx} {d : ihexp} {τ : htyp} →
                       Δ , ∅ ⊢ d :: τ →
                       d dcomplete →
                       okc d Δ
  complete-progress wt comp with progress wt
  complete-progress wt comp | I x = abort (lem-ind-comp comp x)
  complete-progress wt comp | S x = S x
  complete-progress wt comp | BV (BVVal x) = V x
  complete-progress wt (DCCast comp x₂ ()) | BV (BVHoleCast x x₁)
  complete-progress (TACast wt x) (DCCast comp x₃ x₄) | BV (BVArrCast x₁ x₂) = abort (x₁ (eq-complete-consist x₃ x₄ x))
