open import Nat
open import Prelude
open import core

module final-decidable where
  var-not-final : (n : Nat) → X n final → ⊥
  var-not-final n (FBoxed (BVVal ()))
  var-not-final n (FIndet ())

  nehole-not-final : ∀{d x} → (d final → ⊥)  → ⦇ d ⦈⟨ x ⟩ final  → ⊥
  nehole-not-final nf (FBoxed (BVVal ()))
  nehole-not-final nf (FIndet (INEHole x)) = nf x

  ap1-not-final : ∀{d1 d2} → (d1 final → ⊥)  → (d1 ∘ d2) final  → ⊥
  ap1-not-final nf (FBoxed (BVVal ()))
  ap1-not-final nf (FIndet (IAp x x₁ x₂)) = nf (FIndet x₁)

  ap2-not-final : ∀{d1 d2} → (d2 final → ⊥)  → (d1 ∘ d2) final  → ⊥
  ap2-not-final nf (FBoxed (BVVal ()))
  ap2-not-final nf (FIndet (IAp x x₁ x₂)) = nf x₂
  cast-not-final : ∀{d τ1 τ2 } → (d final → ⊥)  → (d ⟨ τ1 ⇒ τ2 ⟩) final → ⊥
  cast-not-final nf (FBoxed (BVVal ()))
  cast-not-final nf (FBoxed (BVArrCast x x₁)) = nf (FBoxed x₁)
  cast-not-final nf (FBoxed (BVHoleCast x x₁)) = nf (FBoxed x₁)
  cast-not-final nf (FIndet (ICastArr x x₁)) = nf (FIndet x₁)
  cast-not-final nf (FIndet (ICastGroundHole x x₁)) = nf (FIndet x₁)
  cast-not-final nf (FIndet (ICastHoleGround x x₁ x₂)) = nf (FIndet x₁)

  failedcast-not-final : ∀{d τ1 τ2 } → (d final → ⊥)  → (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) final → ⊥
  failedcast-not-final nf (FBoxed (BVVal ()))
  failedcast-not-final nf (FIndet (IFailedCast x x₁ x₂ x₃)) = nf x

  final-decidable : (d : dhexp) → (d final) + (d final → ⊥)
  final-decidable c = Inl (FBoxed (BVVal VConst))
  final-decidable (X x) = Inr (var-not-final x)
  final-decidable (·λ x [ x₁ ] d) = Inl (FBoxed (BVVal VLam))
  final-decidable ⦇⦈⟨ x ⟩ = Inl (FIndet IEHole)
  final-decidable ⦇ d ⦈⟨ x ⟩ with final-decidable d
  final-decidable ⦇ d ⦈⟨ x₁ ⟩ | Inl x = Inl (FIndet (INEHole x))
  final-decidable ⦇ d ⦈⟨ x₁ ⟩ | Inr x = Inr (nehole-not-final x)
  final-decidable (d1 ∘ d2) with final-decidable d1 | final-decidable d2
  final-decidable (d1 ∘ d2) | Inl (FBoxed x) | Inl x₁ = {!!}
  final-decidable (d1 ∘ d2) | Inl (FIndet x) | Inl x₁ = {!!}
  final-decidable (d1 ∘ d2) | _ | Inr x = Inr (ap2-not-final x)
  final-decidable (d1 ∘ d2) | Inr x | _ = Inr (ap1-not-final x)
  final-decidable (d ⟨ x ⇒ x₁ ⟩) with final-decidable d
  final-decidable (d ⟨ x₁ ⇒ x₂ ⟩) | Inl x = {!!}
  final-decidable (d ⟨ x₁ ⇒ x₂ ⟩) | Inr x = Inr (cast-not-final x)
  final-decidable (d ⟨ x ⇒⦇⦈⇏ x₁ ⟩) with final-decidable d
  final-decidable (d ⟨ x₁ ⇒⦇⦈⇏ x₂ ⟩) | Inl x = {!!}
  final-decidable (d ⟨ x₁ ⇒⦇⦈⇏ x₂ ⟩) | Inr x = Inr (failedcast-not-final x)
