open import Nat
open import Prelude
open import List
open import core
open import contexts

module progress where

  -- this is a little bit of syntactic sugar to avoid many layer nested Inl
  -- and Inrs that you would get from the more literal transcription of the
  -- consequent of progress as:
  --
  -- d val + d indet + d err[ Δ ] + Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d')
  data ok : (d : dhexp) (Δ : hctx) → Set where
    V : ∀{d Δ} → d val → ok d Δ
    I : ∀{d Δ} → d indet → ok d Δ
    E : ∀{d Δ} → d err[ Δ ] → ok d Δ
    S : ∀{d Δ} → Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d') → ok d Δ

  progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ → ok d Δ
  progress TAConst = V VConst
  progress (TAVar x) = abort (somenotnone (! x))
  progress (TALam D) = V VLam
  progress (TAAp D1 x D2)
    with progress D1 | progress D2
  progress (TAAp TAConst () D2) | V VConst | V x₁
  progress {Δ = Δ} (TAAp D1 x₂ D2) | V VLam | V x₁ = S {Δ = Δ} (_ , Step FRefl (ITLam (FVal x₁)) FRefl)
  progress (TAAp D1 x₂ D2) | V x | I x₁ = {!!}
  progress (TAAp D1 x₂ D2) | V x | E x₁ = {!!}
  progress (TAAp D1 x₂ D2) | V x | S x₁ = {!!}
  progress (TAAp D1 x₂ D2) | I x | V x₁ = {!!}
  progress (TAAp D1 x₂ D2) | I x | I x₁ = {!!}
  progress (TAAp D1 x₂ D2) | I x | E x₁ = {!!}
  progress (TAAp D1 x₂ D2) | I x | S x₁ = {!!}
  progress (TAAp D1 x₂ D2) | E x | V x₁ = {!!}
  progress (TAAp D1 x₂ D2) | E x | I x₁ = {!!}
  progress (TAAp D1 x₂ D2) | E x | E x₁ = {!!}
  progress (TAAp D1 x₂ D2) | E x | S x₁ = {!!}
  progress (TAAp D1 x₂ D2) | S x | V x₁ = {!!}
  progress (TAAp D1 x₂ D2) | S x | I x₁ = {!!}
  progress (TAAp D1 x₂ D2) | S x | E x₁ = {!!}
  progress (TAAp D1 x₂ D2) | S x | S x₁ = {!!}
  progress (TAEHole x x₁) = I IEHole
  progress (TANEHole x D x₁)
    with progress D
  progress (TANEHole x₁ D x₂) | V x = {!!}
  progress (TANEHole x₁ D x₂) | I x = {!!}
  progress (TANEHole x₁ D x₂) | E x = {!!}
  progress (TANEHole x₁ D x₂) | S x = {!!}
  progress (TACast D x)
    with progress D
  progress (TACast TAConst TCRefl)  | V VConst = E {!!}
  progress (TACast TAConst TCHole2) | V VConst = E {!!}
  progress (TACast D x₁) | V VLam = {!!}
  progress (TACast D x₁) | I x = {!!}
  progress (TACast D x₁) | E x = {!!}
  progress (TACast D x₃) | S (d , Step x x₁ x₂) = {!!}
