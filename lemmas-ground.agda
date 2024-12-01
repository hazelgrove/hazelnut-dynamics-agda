open import Nat
open import Prelude
open import core-type
open import core
open import eq-dec

module lemmas-ground where

  ground-arr-not-hole : ∀{τ} →
    (τ ground → ⊥) →
    (τ ≠ (⦇-⦈ ==> ⦇-⦈))
  ground-arr-not-hole notg refl = notg GArr

  ground-forall-not-hole : ∀{τ} →
    (τ ground → ⊥) →
    (τ ≠ (·∀ ⦇-⦈))
  ground-forall-not-hole notg refl = notg GForall

  ground-neq~ : ∀{τ1 τ2} → τ1 ground → τ2 ground → τ1 ≠ τ2 → τ1 ~̸ τ2
  ground-neq~ GBase GBase neq = λ _ → neq refl 
  ground-neq~ GBase GArr neq = λ ()
  ground-neq~ GBase GForall neq = λ ()
  ground-neq~ GArr GBase neq = λ ()
  ground-neq~ GArr GArr neq = λ _ → neq refl
  ground-neq~ GArr GForall neq = λ ()
  ground-neq~ GForall GBase neq = λ ()
  ground-neq~ GForall GArr neq = λ ()
  ground-neq~ GForall GForall neq = λ _ → neq refl

  ground-not-hole : ∀{τ} →
    τ ground → τ ≠ ⦇-⦈
  ground-not-hole GBase = λ ()
  ground-not-hole GArr = λ ()
  ground-not-hole GForall = λ ()

  gnd-gnd-consis-eq : ∀{τ1 τ2} →
    τ1 ground → τ2 ground → τ1 ~ τ2 →
    τ1 == τ2
  gnd-gnd-consis-eq GBase GBase consis = refl
  gnd-gnd-consis-eq GArr GArr consis = refl
  gnd-gnd-consis-eq GForall GForall consis = refl

  ground-match : ∀{τ τ'} →
    τ ▸gnd τ' →
    τ' ground
  ground-match (MGArr x) = GArr
  ground-match (MGForall x) = GForall

  ground-match-exists : ∀{τ} →
    ¬(τ ground) → ∅ ⊢ τ wf → τ ≠ ⦇-⦈ →
    Σ[ τ' ∈ htyp ](τ ▸gnd τ')
  ground-match-exists {b} g _ _ = abort (g GBase)
  ground-match-exists {T x} g () _
  ground-match-exists {⦇-⦈} g wf ne = abort (ne refl)
  ground-match-exists {τ ==> τ₁} g wf ne with htyp-eq-dec (τ ==> τ₁) (⦇-⦈ ==> ⦇-⦈)
  ... | Inl refl = abort (g GArr)
  ... | Inr neq = ⦇-⦈ ==> ⦇-⦈ , MGArr neq
  ground-match-exists {·∀ τ} g wf ne with htyp-eq-dec (·∀ τ) (·∀ ⦇-⦈)
  ... | Inl refl = abort (g GForall)
  ... | Inr neq = ·∀ ⦇-⦈ , MGForall neq

  consist-ground-consist : ∀{τ1 τ2 τ2'} →
    τ1 ~ τ2 → τ2 ▸gnd τ2' → τ1 ~ τ2'
  consist-ground-consist ConsistBase ()
  consist-ground-consist ConsistVar ()
  consist-ground-consist ConsistHole1 ()
  consist-ground-consist ConsistHole2 _ = ConsistHole2
  consist-ground-consist (ConsistArr consis consis₁) (MGArr x) = ConsistArr ConsistHole1 ConsistHole1
  consist-ground-consist (ConsistForall consis) (MGForall x) = ConsistForall ConsistHole1

  ground-match-neq : ∀{τ1 τ2} →
    τ1 ▸gnd τ2 → τ1 ≠ τ2
  ground-match-neq (MGArr x) = x
  ground-match-neq (MGForall x) = x

  gnd-ngnd-neq : ∀{τ1 τ2} →
    τ1 ground → ¬(τ2 ground) → τ1 ≠ τ2
  gnd-ngnd-neq {τ2 = b} GBase ngd = λ _ → ngd GBase
  gnd-ngnd-neq {τ2 = b} GArr ngd = λ ()
  gnd-ngnd-neq {τ2 = b} GForall ngd = λ ()
  gnd-ngnd-neq {τ2 = T x} GBase ngd = λ ()
  gnd-ngnd-neq {τ2 = T x} GArr ngd = λ ()
  gnd-ngnd-neq {τ2 = T x} GForall ngd = λ ()
  gnd-ngnd-neq {τ2 = ⦇-⦈} GBase ngd = λ ()
  gnd-ngnd-neq {τ2 = ⦇-⦈} GArr ngd = λ ()
  gnd-ngnd-neq {τ2 = ⦇-⦈} GForall ngd = λ ()
  gnd-ngnd-neq {τ2 = τ2 ==> τ3} GBase ngd = λ ()
  gnd-ngnd-neq {τ2 = τ2 ==> τ3} GArr ngd x rewrite ! x = ngd GArr
  gnd-ngnd-neq {τ2 = τ2 ==> τ3} GForall ngd = λ ()
  gnd-ngnd-neq {τ2 = ·∀ τ2} gnd ngd x rewrite ! x = ngd gnd
