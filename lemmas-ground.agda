open import Prelude
open import core

module lemmas-ground where
  ground-arr-not-hole : ∀{τ} →
                      (τ ground → ⊥) →
                      (τ ≠ (⦇⦈ ==> ⦇⦈))
  ground-arr-not-hole notg refl = notg GHole

  notground : ∀{τ} → (τ ground → ⊥) → (τ == ⦇⦈) + (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] (τ == (τ1 ==> τ2)))
  notground {b} gnd = abort (gnd GBase)
  notground {⦇⦈} gnd = Inl refl
  notground {b ==> b} gnd = Inr (b , b , refl)
  notground {b ==> ⦇⦈} gnd = Inr (b , ⦇⦈ , refl)
  notground {b ==> τ2 ==> τ3} gnd = Inr (b , τ2 ==> τ3 , refl)
  notground {⦇⦈ ==> b} gnd = Inr (⦇⦈ , b , refl)
  notground {⦇⦈ ==> ⦇⦈} gnd = abort (gnd GHole)
  notground {⦇⦈ ==> τ2 ==> τ3} gnd = Inr (⦇⦈ , τ2 ==> τ3 , refl)
  notground {(τ1 ==> τ2) ==> b} gnd = Inr (τ1 ==> τ2 , b , refl)
  notground {(τ1 ==> τ2) ==> ⦇⦈} gnd = Inr (τ1 ==> τ2 , ⦇⦈ , refl)
  notground {(τ1 ==> τ2) ==> τ3 ==> τ4} gnd = Inr (τ1 ==> τ2 , τ3 ==> τ4 , refl)
