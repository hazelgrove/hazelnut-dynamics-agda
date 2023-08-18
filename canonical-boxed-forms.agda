open import Nat
open import Prelude
open import contexts
open import core

open import canonical-value-forms

module canonical-boxed-forms where

  canonical-boxed-forms-b : ∀{Δ d} →
                            Δ , ∅ , ∅ ⊢ d :: b →
                            d boxedval →
                            d == c
  canonical-boxed-forms-b (TAVar _) (BVVal ())
  canonical-boxed-forms-b wt (BVVal v) = canonical-value-forms-b wt v

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for boxed values at arrow type
  data cbf-arr : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CBFLam : ∀{Δ d τ1 τ2} →
      (Σ[ x ∈ Nat ] Σ[ d' ∈ ihexp ]
         (d == (·λ x [ τ1 ] d') × Δ , ∅ , ■ (x , τ1) ⊢ d' :: τ2))
      → cbf-arr Δ d τ1 τ2
    CBFCastArr : ∀{Δ d τ1 τ2} →
      (Σ[ d' ∈ ihexp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
         (d == (d' ⟨ τ1' ==> τ2' ⇒ τ1 ==> τ2 ⟩) ×
         (τ1' ==> τ2' =α̸  τ1 ==> τ2) ×
         (Δ , ∅ , ∅ ⊢ d' :: τ1' ==> τ2')))
      → cbf-arr Δ d τ1 τ2

  canonical-boxed-forms-arr : ∀{Δ d τ1 τ2 } →
                            Δ , ∅ , ∅ ⊢ d :: (τ1 ==> τ2)  →
                            d boxedval →
                            cbf-arr Δ d τ1 τ2
  canonical-boxed-forms-arr (TAVar x₁) (BVVal ())
  canonical-boxed-forms-arr (TALam f wf wt) (BVVal v) = CBFLam (canonical-value-forms-arr (TALam f wf wt) v)
  canonical-boxed-forms-arr (TAAp wt wt₁) (BVVal ())
  canonical-boxed-forms-arr (TAEHole x x₁ eq) (BVVal ())
  canonical-boxed-forms-arr (TANEHole x wt x₁ eq) (BVVal ())
  canonical-boxed-forms-arr (TACast wt _ x) (BVVal ())
  canonical-boxed-forms-arr (TACast wt _ x) (BVArrCast x₁ bv) = CBFCastArr (_ , _ , _ , refl , x₁ , wt)
  canonical-boxed-forms-arr (TAFailedCast x x₁ x₂ x₃) (BVVal ())
  
  -- Similar to the arr case, give the two possible forms of a forall type.
  data cbf-forall : (Δ : hctx) (d : ihexp) (t : Nat) (τ : htyp) → Set where
    -- the value case
    CBFTLam : ∀{Δ d t τ} → 
      (Σ[ d' ∈ ihexp ] 
        ((d == (·Λ t d')) ×
        (Δ , (∅ ,, (t , <>)) , ∅ ⊢ d' :: τ)))
      → cbf-forall Δ d t τ
    -- the cast case
    CBFCastForall : ∀{Δ d t2 τ2} →
      (Σ[ d' ∈ ihexp ] Σ[ t1 ∈ Nat ] Σ[ τ1 ∈ htyp ]
        (d == (d' ⟨ ·∀ t1 τ1 ⇒ ·∀ t2 τ2 ⟩) ×
         (·∀ t1 τ1) =α̸  (·∀ t2 τ2) × 
         (Δ , ∅ , ∅ ⊢ d' :: ·∀ t1 τ1)))
      → cbf-forall Δ d t2 τ2
  
  canonical-boxed-forms-forall : ∀{Δ d t τ } →
                            Δ , ∅ , ∅ ⊢ d :: (·∀ t τ)  →
                            d boxedval →
                            cbf-forall Δ d t τ
  canonical-boxed-forms-forall (TATLam wt) (BVVal v) = CBFTLam (canonical-value-forms-typfun (TATLam wt) v)
  canonical-boxed-forms-forall (TACast wt _ x) (BVVal ())
  canonical-boxed-forms-forall {t = t} {τ = τ} (TACast wt _ consist) (BVForallCast neq bv) = CBFCastForall ( _ , _ , _ , refl , neq , wt)

  canonical-boxed-forms-hole : ∀{Δ d} →
                               Δ , ∅ , ∅ ⊢ d :: ⦇-⦈ →
                               d boxedval →
                               Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
                                 ((d == d' ⟨ τ' ⇒ ⦇-⦈ ⟩) ×
                                  (τ' ground) ×
                                  (Δ , ∅ , ∅ ⊢ d' :: τ'))
  canonical-boxed-forms-hole (TAVar x₁) (BVVal ())
  canonical-boxed-forms-hole (TAAp wt wt₁) (BVVal ())
  canonical-boxed-forms-hole (TAEHole x x₁ eq) (BVVal ())
  canonical-boxed-forms-hole (TANEHole x wt x₁ eq) (BVVal ())
  canonical-boxed-forms-hole (TACast wt _ x) (BVVal ())
  canonical-boxed-forms-hole (TACast wt _ x) (BVHoleCast x₁ bv) = _ , _ , refl , x₁ , wt
  canonical-boxed-forms-hole (TAFailedCast x x₁ x₂ x₃) (BVVal ())

  canonical-boxed-forms-coverage : ∀{Δ d τ} →
                                   Δ , ∅ , ∅ ⊢ d :: τ →
                                   d boxedval →
                                   τ ≠ b →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                   τ ≠ ⦇-⦈ →
                                   ((t : Nat) (τ' : htyp) → τ ≠ ·∀ t τ') →
                                   ⊥
  canonical-boxed-forms-coverage TAConst (BVVal x) nb na nh nf = nb refl
  canonical-boxed-forms-coverage (TAVar x₁) (BVVal ()) nb na nh nf
  canonical-boxed-forms-coverage (TALam _ _ wt) (BVVal x₁) nb na nh nf = na _ _ refl
  canonical-boxed-forms-coverage (TATLam x₁) (BVVal x₂) nb na nh nf = nf _ _ refl
  canonical-boxed-forms-coverage (TAAp wt wt₁) (BVVal ()) nb na nh nf
  canonical-boxed-forms-coverage (TAEHole x x₁ eq) (BVVal ()) nb na nh nf
  canonical-boxed-forms-coverage (TANEHole x wt x₁ eq) (BVVal ()) nb na nh nf
  canonical-boxed-forms-coverage (TACast wt _ x) (BVVal ()) nb na nh nf
  canonical-boxed-forms-coverage (TACast wt _ x) (BVArrCast x₁ bv) nb na nh nf = na _ _ refl
  canonical-boxed-forms-coverage (TACast wt _ x) (BVHoleCast x₁ bv) nb na nh nf = nh refl
  canonical-boxed-forms-coverage (TACast wt _ x) (BVForallCast x₁ x₂) nb na nh nf = nf _ _ refl
  canonical-boxed-forms-coverage (TAFailedCast x x₁ x₂ x₃) (BVVal ())
