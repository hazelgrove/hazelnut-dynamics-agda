open import Nat
open import Prelude
open import contexts
open import core
open import type-assignment-unicity

open typctx

module canonical-indeterminate-forms where

  forall-injective : ∀ {m n} → ·∀ m == ·∀ n → m == n
  forall-injective refl = refl

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at base type
  data cif-base : (Δ : hctx) (d : ihexp) → Set where
    CIFBEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: b [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
       → cif-base Δ d
    CIFBNEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: b [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
        → cif-base Δ d
    CIFBAp : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: τ2 ==> b) ×
         (Δ , ~∅ , ∅ ⊢ d2 :: τ2) ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-base Δ d
    CIFBTApBase : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ]
        ((d == d1 < τ >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ b) ×
         (d1 indet) ×
         ((τ1 τ1' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ1) ⇒ (·∀ τ1')⟩))
        )
        → cif-base Δ d
    CIFBTApId : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ]
        ((d == d1 < b >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ (T Z)) ×
         (d1 indet) ×
         ((τ1 τ1' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ1) ⇒ (·∀ τ1')⟩))
        )
        → cif-base Δ d
    CIFBCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ]
        ((d == d' ⟨ ⦇-⦈ ⇒ b ⟩) ×
         (Δ , ~∅ , ∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-base Δ d
    CIFBFailedCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d' ⟨ τ' ⇒⦇-⦈⇏ b ⟩) ×
         (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (τ' ≠ b)
        )
       → cif-base Δ d

  canonical-indeterminate-forms-base : ∀{Δ d} →
                                       Δ , ~∅ , ∅ ⊢ d :: b →
                                       d indet →
                                       cif-base Δ d
--  canonical-indeterminate-forms-base TAConst ()
  canonical-indeterminate-forms-base (TAVar x₁) ()
  canonical-indeterminate-forms-base (TAAp wt wt₁) (IAp x ind x₁) = CIFBAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-base (TATAp {τ2 = b} wf x eq) (ITAp x₃ ind) = CIFBTApBase (_ , _ , refl , x , ind , x₃)
  canonical-indeterminate-forms-base {d = d} (TATAp {τ1 = τ1} {τ2 = T Z} wf x eq) (ITAp x₃ ind) rewrite eq = CIFBTApId (_ , τ1 , refl , x , ind , x₃)
  canonical-indeterminate-forms-base (TAEHole x x₁) IEHole = CIFBEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-base (TANEHole x wt x₁) (INEHole x₂) = CIFBNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-base (TACast wt _ x) (ICastHoleGround x₁ ind x₂) = CIFBCast (_ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-base (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) = CIFBFailedCast (_ , _ , refl , x , x₅ , x₇)

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at arrow type
  data cif-arr : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CIFAEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
      → cif-arr Δ d τ1 τ2
    CIFANEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
        → cif-arr Δ d τ1 τ2
    CIFAAp : ∀{d Δ τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2' ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: τ2' ==> (τ1 ==> τ2)) ×
         (Δ , ~∅ , ∅ ⊢ d2 :: τ2') ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFATApArr : ∀ {Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 < τ >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ (τ1 ==> τ2)) ×
         (d1 indet) ×
         ((τ3 τ3' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ3) ⇒ (·∀ τ3')⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFATApId : ∀ {Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 < τ1 ==> τ2 >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ (T Z)) ×
         (d1 indet) ×
         ((τ3 τ3' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ3) ⇒ (·∀ τ3')⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFACast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == d' ⟨ (τ1' ==> τ2') ⇒ (τ1 ==> τ2) ⟩) ×
          (Δ , ~∅ , ∅ ⊢ d' :: τ1' ==> τ2') ×
          (d' indet) ×
          ((τ1' ==> τ2') ≠ (τ1 ==> τ2))
        )
       → cif-arr Δ d τ1 τ2
    CIFACastHole : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (d' ⟨ ⦇-⦈ ⇒ ⦇-⦈ ==> ⦇-⦈ ⟩)) ×
         (τ1 == ⦇-⦈) ×
         (τ2 == ⦇-⦈) ×
         (Δ , ~∅ , ∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFAFailedCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
          ((d == (d' ⟨ τ' ⇒⦇-⦈⇏ ⦇-⦈ ==> ⦇-⦈ ⟩) ) ×
           (τ1 == ⦇-⦈) ×
           (τ2 == ⦇-⦈) ×
           (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
           (τ' ground) ×
           (τ' ≠ (⦇-⦈ ==> ⦇-⦈))
           )
          → cif-arr Δ d τ1 τ2

  canonical-indeterminate-forms-arr : ∀{Δ d τ1 τ2 } →
                                       Δ , ~∅ , ∅ ⊢ d :: (τ1 ==> τ2) →
                                       d indet →
                                       cif-arr Δ d τ1 τ2
  canonical-indeterminate-forms-arr (TAVar x₁) ()
  canonical-indeterminate-forms-arr (TALam _ _ wt) ()
  canonical-indeterminate-forms-arr (TAAp wt wt₁) (IAp x ind x₁) = CIFAAp (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-arr (TATAp {τ1 = τ1} {τ2 = τ3 ==> τ4} wf wt eq) (ITAp x ind) rewrite eq = CIFATApArr ( _ , τ1 , τ3 , τ4 , refl , wt , ind , x)
  canonical-indeterminate-forms-arr (TATAp {τ2 = T Z} wf wt eq) (ITAp x ind) rewrite eq = CIFATApId ( _ , _ , _ , refl , wt , ind , x )
  canonical-indeterminate-forms-arr (TAEHole x x₁) IEHole = CIFAEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-arr (TANEHole x wt x₁) (INEHole x₂) = CIFANEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-arr (TACast wt _ x) (ICastArr x₁ ind) = CIFACast (_ , _ , _ , _ , _ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-arr (TACast wt _ TCHole2) (ICastHoleGround x₁ ind GArr) = CIFACastHole (_ , refl , refl , refl , wt , ind , x₁)
  canonical-indeterminate-forms-arr (TAFailedCast x x₁ GArr x₃) (IFailedCast x₄ x₅ GArr x₇) = CIFAFailedCast (_ , _ , refl , refl , refl , x , x₅ , x₇)

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at forall type
  data cif-forall : (Δ : hctx) (d : ihexp) (τ : htyp) → Set where
    CIFFEHole : ∀{d Δ τ} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: (·∀ τ) [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
      → cif-forall Δ d τ
    CIFFNEHole : ∀{d Δ τ} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: (·∀ τ) [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
        → cif-forall Δ d τ
    CIFFAp : ∀{d Δ τ} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: τ' ==> (·∀ τ)) ×
         (Δ , ~∅ , ∅ ⊢ d2 :: τ') ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-forall Δ d τ
    CIFFTApForall : ∀ {Δ d τ} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ] Σ[ τ' ∈ htyp ] 
        ((d == d1 < τ >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ (·∀ τ')) ×
         (d1 indet) ×
         ((τ2 τ2' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ2) ⇒ (·∀ τ2')⟩))
        )
        → cif-forall Δ d τ
    CIFFTApId : ∀ {Δ d τ} →
      Σ[ d1 ∈ ihexp ] Σ[ τ1 ∈ htyp ]
        ((d == d1 < ·∀ τ1 >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ (T Z)) ×
         (d1 indet) ×
         ((τ3 τ3' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ3) ⇒ (·∀ τ3')⟩))
        )
        → cif-forall Δ d τ
    CIFFCast : ∀{d Δ τ} →
      Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ1' ∈ htyp ]
        ((d == d' ⟨ (·∀ τ1') ⇒ (·∀ τ1) ⟩) ×
          (Δ , ~∅ , ∅ ⊢ d' :: ·∀ τ1') ×
          (d' indet) ×
          ((·∀ τ1') ≠ (·∀ τ1))
        )
       → cif-forall Δ d τ
    CIFFCastHole : ∀{d Δ τ} →
      Σ[ d' ∈ ihexp ]
        ((d == (d' ⟨ ⦇-⦈ ⇒ ·∀ ⦇-⦈ ⟩)) ×
         (τ == ⦇-⦈) ×
         (Δ , ~∅ , ∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-forall Δ d τ
    CIFFFailedCast : ∀{d Δ τ} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
          ((d == (d' ⟨ τ' ⇒⦇-⦈⇏ ·∀ ⦇-⦈ ⟩) ) ×
           (τ == ⦇-⦈) ×
           (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
           (τ' ground) ×
           (τ' ≠ (·∀ ⦇-⦈))
           )
          → cif-forall Δ d τ

  canonical-indeterminate-forms-forall : ∀{Δ d τ} →
                                       Δ , ~∅ , ∅ ⊢ d :: (·∀ τ) →
                                       d indet →
                                       cif-forall Δ d τ
  -- canonical-indeterminate-forms-forall = {!   !}
  canonical-indeterminate-forms-forall (TAVar x₁) ()
  canonical-indeterminate-forms-forall (TAAp wt wt₁) (IAp x ind x₁) = CIFFAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-forall (TATAp {τ1 = τ1} {τ2 = ·∀ τ3} wf wt eq) (ITAp x ind) rewrite eq = CIFFTApForall ( _ , _ , _ , refl , wt , ind , x)
  canonical-indeterminate-forms-forall (TATAp {τ2 = T Z} wf wt eq) (ITAp x ind) rewrite eq = CIFFTApId ( _ , _ , refl , wt , ind , x )
  canonical-indeterminate-forms-forall (TAEHole x x₁) IEHole = CIFFEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-forall (TANEHole x wt x₁) (INEHole x₂) = CIFFNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-forall (TACast wt _ x) (ICastForall x₁ ind) = CIFFCast (_ , _ , _ , refl , wt , ind , λ x₃ → x₁ (forall-injective x₃) )
  canonical-indeterminate-forms-forall (TACast wt _ TCHole2) (ICastHoleGround x₁ ind GForall) = CIFFCastHole (_ , refl , refl , wt , ind , x₁)
  canonical-indeterminate-forms-forall (TAFailedCast x x₁ GForall x₃) (IFailedCast x₄ x₅ GForall x₇) = CIFFFailedCast (_ , _ , refl , refl , x , x₅ , x₇)


  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at hole type
  data cif-hole : (Δ : hctx) (d : ihexp) → Set where
    CIFHEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: ⦇-⦈ [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
      → cif-hole Δ d
    CIFHNEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: ⦇-⦈ [ Γ ]) ∈ Δ) ×
         (Δ , ~∅ , ∅ ⊢ σ :s: Γ)
        )
      → cif-hole Δ d
    CIFHAp : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: (τ2 ==> ⦇-⦈)) ×
         (Δ , ~∅ , ∅ ⊢ d2 :: τ2) ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
      → cif-hole Δ d
    CIFHTApHole : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ]
        ((d == d1 < τ >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ ⦇-⦈) ×
         (d1 indet) ×
         ((τ1 τ1' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ1) ⇒ (·∀ τ1')⟩))
        )
        → cif-hole Δ d
    CIFHTApId : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ]
        ((d == d1 < ⦇-⦈ >) ×
         (Δ , ~∅ , ∅ ⊢ d1 :: ·∀ (T Z)) ×
         (d1 indet) ×
         ((τ1 τ1' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ1) ⇒ (·∀ τ1')⟩))
        )
        → cif-hole Δ d
    CIFHCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d' ⟨ τ' ⇒ ⦇-⦈ ⟩) ×
         (Δ , ~∅ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (d' indet)
        )
      → cif-hole Δ d

  canonical-indeterminate-forms-hole : ∀{Δ d} →
                                       Δ , ~∅ , ∅ ⊢ d :: ⦇-⦈ →
                                       d indet →
                                       cif-hole Δ d
  canonical-indeterminate-forms-hole (TAVar x₁) ()
  canonical-indeterminate-forms-hole (TAAp wt wt₁) (IAp x ind x₁) = CIFHAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-hole (TATAp {τ2 = ⦇-⦈} wf wt wt₁) (ITAp x ind) = CIFHTApHole ( _ , (_ , (refl , (wt , ind , x))) )
  canonical-indeterminate-forms-hole (TATAp {τ1 = τ1} {τ2 = T Z} wf wt eq) (ITAp x ind) rewrite eq = CIFHTApId ( _ , (τ1 , (refl , (wt , ind , x))) )
  canonical-indeterminate-forms-hole (TAEHole x x₁) IEHole = CIFHEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-hole (TANEHole x wt x₁) (INEHole x₂) = CIFHNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-hole (TACast wt wf x) (ICastGroundHole x₁ ind) = CIFHCast (_ , _ , refl , wt , x₁ , ind)
  canonical-indeterminate-forms-hole (TACast wt wf x) (ICastHoleGround x₁ ind ())
  canonical-indeterminate-forms-hole (TAFailedCast x x₁ () x₃) (IFailedCast x₄ x₅ x₆ x₇)

  canonical-indeterminate-forms-coverage : ∀{Δ d τ} →
                                           Δ , ~∅ , ∅ ⊢ d :: τ →
                                           d indet →
                                           τ ≠ b →
                                           ((n : Nat) → τ ≠ (T n)) →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                           τ ≠ ⦇-⦈ →
                                           ((τ1 : htyp)  → τ ≠ (·∀ τ1)) →
                                           ⊥
  canonical-indeterminate-forms-coverage {τ = b} _ _ nb _ _ nf nh = nb refl
  canonical-indeterminate-forms-coverage {τ = T x} _ _ nb nv na nf nh = nv x refl
  canonical-indeterminate-forms-coverage {τ = ⦇-⦈} _ _ nb nv na nf nh = nf refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} _ _ nb nv na nf nh = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = ·∀ τ} _ _ nb nv na nf nh = nh τ refl