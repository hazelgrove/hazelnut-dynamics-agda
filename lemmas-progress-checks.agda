open import Nat
open import Prelude
open import List
open import core

module lemmas-progress-checks where
  ce-castarr : ∀{d τ1 τ2 τ3 τ4} → (d ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩) casterr → d casterr
  ce-castarr (CECong FHOuter ce) = ce-castarr ce
  ce-castarr (CECong (FHCast x₁) ce) = CECong x₁ ce

  ce-castth : ∀{d τ} → (d ⟨ τ ⇒ ⦇⦈ ⟩) casterr → d casterr
  ce-castth (CECastFail x₁ x₂ () x₄)
  ce-castth (CECong FHOuter ce) = ce-castth ce
  ce-castth (CECong (FHCast x₁) ce) = CECong x₁ ce

  ce-nehole : ∀{d u σ} → ⦇ d ⦈⟨ u , σ ⟩ casterr → d casterr
  ce-nehole (CECong FHOuter ce) = ce-nehole ce
  ce-nehole (CECong (FHNEHole x₁) ce) = CECong x₁ ce

  ce-ap : ∀{d1 d2} → (d1 ∘ d2) casterr → (d1 casterr + d2 casterr)
  ce-ap (CECong FHOuter ce) = ce-ap ce
  ce-ap (CECong (FHAp1 x₂) ce) = Inl (CECong x₂ ce)
  ce-ap (CECong (FHAp2 x₂ x₃) ce) = Inr (CECong x₃ ce)

  ce-castht : ∀{d τ} → (d ⟨ ⦇⦈ ⇒ τ ⟩) casterr → ((d' : dhexp) (τ' : htyp) → d ≠ (d' ⟨ τ' ⇒ ⦇⦈ ⟩)) → d casterr
  ce-castht (CECastFail x₂ x₃ x₄ x₅) f = abort (f _ _ refl)
  ce-castht (CECong FHOuter ce) = ce-castht ce
  ce-castht (CECong (FHCast x₂) ce) _ = CECong x₂ ce
