open import Nat
open import Prelude
open import List
open import core
open import contexts

module complete-progress where

  data ok : (d : dhexp) (Δ : hctx) → Set where
    V : ∀{d Δ} → d val → ok d Δ
    S : ∀{d Δ} → Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d') → ok d Δ

  -- nb: don't need (Δ , ∅ ⊢ d :: τ) because of typed-expansion
  complete-progress : {Δ : hctx} {d : dhexp} {τ : htyp} {e : hexp}→
                       ecomplete e →
                       ∅ ⊢ e ⇒ τ ~> d ⊣ Δ →
                       ok d Δ
  complete-progress = {!!}
