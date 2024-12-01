open import Prelude
open import core-type
open import core

module ground-dec where
  
  ground-dec : (τ : htyp) → (τ ground) + ¬(τ ground)
  ground-dec b = Inl GBase
  ground-dec ⦇-⦈ = Inr (λ ())
  ground-dec (⦇-⦈ ==> ⦇-⦈) = Inl GArr
  ground-dec (b ==> _) = Inr (λ ())
  ground-dec (_ ==> b) = Inr (λ ())
  ground-dec ((_ ==> _) ==> _) = Inr (λ ())
  ground-dec (_ ==> (_ ==> _)) = Inr (λ ())
  ground-dec ((·∀ _) ==> _) = Inr (λ ())
  ground-dec (_ ==> (·∀ _)) = Inr (λ ())
  ground-dec (·∀ ⦇-⦈) = Inl GForall
  ground-dec (·∀ b) = Inr (λ ())
  ground-dec (·∀ (T _)) = Inr (λ ())
  ground-dec (·∀ (_ ==> _)) = Inr (λ ())
  ground-dec (·∀ (·∀ _)) = Inr (λ ())
  ground-dec (T _) = Inr (λ ())
  ground-dec ((T _) ==> _) = Inr (λ ())
  ground-dec (_ ==> (T _)) = Inr (λ ())
