open import Nat
open import Prelude
open import contexts
open import core

open import canonical-value-forms

module canonical-boxed-forms where
  canonical-boxed-forms-b : ∀{Δ d} →
                            Δ , ∅ ⊢ d :: b →
                            d boxedval →
                            d == c
  canonical-boxed-forms-b (TAVar _) (BVVal ())
  canonical-boxed-forms-b (TAAp _ _) (BVVal ())
  canonical-boxed-forms-b (TAEHole _ _) (BVVal ())
  canonical-boxed-forms-b (TANEHole _ _ _) (BVVal ())
  canonical-boxed-forms-b (TACast _ _) (BVVal ())
  canonical-boxed-forms-b wt (BVVal v) = canonical-value-forms-b wt v

  canonical-boxed-forms-arr : ∀{Δ d τ1 τ2 } →
                            Δ , ∅ ⊢ d :: (τ1 ==> τ2)  →
                            d boxedval →
                            (Σ[ x ∈ Nat ] Σ[ d' ∈ dhexp ] (d == (·λ x [ τ1 ] d') ×
                                                           Δ , ■ (x , τ1) ⊢ d' :: τ2)) +
                            (Σ[ d' ∈ dhexp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ] (d == (d' ⟨ τ1' ==> τ2' ⇒ τ1 ==> τ2 ⟩) ×
                                                                             (τ1' ==> τ2' ≠ τ1 ==> τ2) ×
                                                                             (Δ , ∅ ⊢ d' :: τ1' ==> τ2')))
  canonical-boxed-forms-arr (TAVar x₁) (BVVal ())
  canonical-boxed-forms-arr (TALam wt) (BVVal v) = Inl (canonical-value-forms-arr (TALam wt) v)
  canonical-boxed-forms-arr (TAAp wt wt₁) (BVVal ())
  canonical-boxed-forms-arr (TAEHole x x₁) (BVVal ())
  canonical-boxed-forms-arr (TANEHole x wt x₁) (BVVal ())
  canonical-boxed-forms-arr (TACast wt x) (BVVal ())
  canonical-boxed-forms-arr (TACast wt x) (BVArrCast x₁ bv) = Inr (_ , _ , _ , refl , x₁ , wt)

  canonical-boxed-forms-hole : ∀{Δ d} →
                               Δ , ∅ ⊢ d :: ⦇⦈ →
                               d boxedval →
                               Σ[ d' ∈ dhexp ] Σ[ τ' ∈ htyp ] ((d == d' ⟨ τ' ⇒ ⦇⦈ ⟩) ×
                                                               (τ' ground) ×
                                                               (Δ , ∅ ⊢ d' :: τ'))
  canonical-boxed-forms-hole (TAVar x₁) (BVVal ())
  canonical-boxed-forms-hole (TAAp wt wt₁) (BVVal ())
  canonical-boxed-forms-hole (TAEHole x x₁) (BVVal ())
  canonical-boxed-forms-hole (TANEHole x wt x₁) (BVVal ())
  canonical-boxed-forms-hole (TACast wt x) (BVVal ())
  canonical-boxed-forms-hole (TACast wt x) (BVHoleCast x₁ bv) = _ , _ , refl , x₁ , wt

  canonical-boxed-forms-coverage : ∀{Δ d τ} →
                                   Δ , ∅ ⊢ d :: τ →
                                   d boxedval →
                                   τ ≠ b →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                   τ ≠ ⦇⦈ →
                                   ⊥
  canonical-boxed-forms-coverage TAConst (BVVal x) nb na nh = nb refl
  canonical-boxed-forms-coverage (TAVar x₁) (BVVal ()) nb na nh
  canonical-boxed-forms-coverage (TALam wt) (BVVal x₁) nb na nh = na _ _ refl
  canonical-boxed-forms-coverage (TAAp wt wt₁) (BVVal ()) nb na nh
  canonical-boxed-forms-coverage (TAEHole x x₁) (BVVal ()) nb na nh
  canonical-boxed-forms-coverage (TANEHole x wt x₁) (BVVal ()) nb na nh
  canonical-boxed-forms-coverage (TACast wt x) (BVVal ()) nb na nh
  canonical-boxed-forms-coverage (TACast wt x) (BVArrCast x₁ bv) nb na nh = na _ _ refl
  canonical-boxed-forms-coverage (TACast wt x) (BVHoleCast x₁ bv) nb na nh = nh refl