open import Nat
open import Prelude
open import List
open import core
open import contexts

module progress where
  progress : {Δ : hctx} {d : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             d val + d indet + d err[ Δ ] + Σ[ d' ∈ dhexp ] (Δ ⊢ d ↦ d') -- todo : make this a record so this is readable
  progress TAConst = Inl VConst
  progress (TAVar x₁) = abort (somenotnone (! x₁))
  progress (TALam D) = Inl VLam
  progress (TAAp D x D₁) with progress D | progress D₁
  progress (TAAp D x₂ D₁) | Inl x | Inl x₁ = Inr (Inr (Inr (_ , (Step {!!} {!!} {!!}))))
  progress (TAAp D x₂ D₁) | Inl x | Inr (Inl x₁) = {!!}
  progress (TAAp D x₂ D₁) | Inl x | Inr (Inr (Inl x₁)) = {!!}
  progress (TAAp D x₂ D₁) | Inl x | Inr (Inr (Inr x₁)) = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inl x) | Inl x₁ = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inl x)) | Inl x₁ = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inr x)) | Inl x₁ = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inl x) | Inr (Inl x₁) = {!!}
  progress (TAAp D x₁ D₁) | Inr (Inl x) | Inr (Inr ih2) = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inl x)) | Inr (Inl x₁) = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inr x)) | Inr (Inl x₁) = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inl x)) | Inr (Inr (Inl x₁)) = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inl x)) | Inr (Inr (Inr x₁)) = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inr x)) | Inr (Inr (Inl x₁)) = {!!}
  progress (TAAp D x₂ D₁) | Inr (Inr (Inr x)) | Inr (Inr (Inr x₁)) = {!!}
  progress (TAEHole x x₁) = Inr (Inl IEHole)
  progress (TANEHole x D x₁) with progress D
  progress (TANEHole x₁ D x₂) | Inl x = {!!}
  progress (TANEHole x₁ D x₂) | Inr (Inl x) = {!!}
  progress (TANEHole x₁ D x₂) | Inr (Inr (Inl x)) = {!!}
  progress (TANEHole x₁ D x₂) | Inr (Inr (Inr x)) = {!!}
  progress (TACast D x) with progress D
  progress (TACast D x₁) | Inl x = Inr (Inr (Inr (_ , Step FRefl (ITCast (FVal x) D x₁) FRefl)))
  progress (TACast D x₁) | Inr (Inl x) = Inr (Inl (ICast x))
  progress (TACast D x₁) | Inr (Inr (Inl x)) = Inr (Inr (Inl {!!} ))
  progress (TACast D x₁) | Inr (Inr (Inr x)) = {!!}
