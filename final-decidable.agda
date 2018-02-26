open import Nat
open import Prelude
open import core

module final-decidable where
  var-not-final : (n : Nat) → X n final → ⊥
  var-not-final n (FBoxed (BVVal ()))
  var-not-final n (FIndet ())

  final-decidable : (d : dhexp) → (d final) + (d final → ⊥)
  final-decidable c = Inl (FBoxed (BVVal VConst))
  final-decidable (X x) = Inr (var-not-final x)
  final-decidable (·λ x [ x₁ ] d) = Inl (FBoxed (BVVal VLam))
  final-decidable ⦇⦈⟨ x ⟩ = Inl (FIndet IEHole)
  final-decidable ⦇ d ⦈⟨ x ⟩ = Inl (FIndet (INEHole {!!}))
  final-decidable (d ∘ d₁) = {!!}
  final-decidable (d ⟨ x ⇒ x₁ ⟩) = {!!}
  final-decidable (d ⟨ x ⇒⦇⦈⇏ x₁ ⟩) = {!!}
