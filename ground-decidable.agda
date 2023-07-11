open import Prelude
open import core

module ground-decidable where
  ground-decidable : (τ : htyp) → (τ ground) + ¬(τ ground)
  ground-decidable b = Inl GBase
  ground-decidable ⦇-⦈ = Inr (λ ())
  ground-decidable (⦇-⦈ ==> ⦇-⦈) = Inl GHole
  ground-decidable (b ==> _) = Inr (λ ())
  ground-decidable (_ ==> b) = Inr (λ ())
  ground-decidable ((_ ==> _) ==> _) = Inr (λ ())
  ground-decidable (_ ==> (_ ==> _)) = Inr (λ ())
  ground-decidable ((·∀ _) ==> _) = Inr (λ ())
  ground-decidable (_ ==> (·∀ _)) = Inr (λ ())
  ground-decidable (·∀ ⦇-⦈) = Inl GForall
  ground-decidable (·∀ b) = Inr (λ ())
  ground-decidable (·∀ (T _)) = Inr (λ ())
  ground-decidable (·∀ (_ ==> _)) = Inr (λ ())
  ground-decidable (·∀ (·∀ _)) = Inr (λ ())
  ground-decidable (T _) = Inr (λ ())
  ground-decidable ((T _) ==> _) = Inr (λ ())
  ground-decidable (_ ==> (T _)) = Inr (λ ())
  -- I don't know where this is used
  -- ground-arr-lem : (τ : htyp) → ((τ ground) → ⊥) → (τ ≠  ⦇-⦈) → Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] ((τ == (τ1 ==> τ2)) × ((τ1 ==> τ2) ≠ (⦇-⦈ ==> ⦇-⦈)))
  -- ground-arr-lem b ng nh = abort (ng GBase)
  -- ground-arr-lem ⦇-⦈ ng nh = abort (nh refl)
  -- ground-arr-lem (τ1 ==> τ2) ng nh = τ1 , τ2 , refl , (λ x → ng (lem' x))
  --   where
  --     lem' : ∀{τ1 τ2} → τ1 ==> τ2 == ⦇-⦈ ==> ⦇-⦈ → (τ1 ==> τ2) ground
  --     lem' refl = GHole
