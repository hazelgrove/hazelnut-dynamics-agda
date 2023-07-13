open import Nat
open import Prelude
open import contexts
open import core
open import type-assignment-unicity

open typctx

module canonical-indeterminate-forms where

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at base type
  data cif-base : (Δ : hctx) (d : ihexp) → Set where
    CIFBEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: b [ Γ ]) ∈ Δ) ×
         (Δ , ∅ , ~∅ ⊢ σ :s: Γ)
        )
       → cif-base Δ d
    CIFBNEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ , ~∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: b [ Γ ]) ∈ Δ) ×
         (Δ , ∅ , ~∅ ⊢ σ :s: Γ)
        )
        → cif-base Δ d
    CIFBAp : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ , ~∅ ⊢ d1 :: τ2 ==> b) ×
         (Δ , ∅ , ~∅ ⊢ d2 :: τ2) ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-base Δ d
    CIFBTApBase : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ]
        ((d == d1 < τ >) ×
         (Δ , ∅ , ~∅ ⊢ d1 :: ·∀ b) ×
         (d1 indet) ×
         ((τ1 τ1' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ1) ⇒ (·∀ τ1')⟩))
        )
        → cif-base Δ d
    CIFBTApId : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ τ ∈ htyp ]
        ((d == d1 < b >) ×
         (Δ , ∅ , ~∅ ⊢ d1 :: ·∀ (T Z)) ×
         (d1 indet) ×
         ((τ1 τ1' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨(·∀ τ1) ⇒ (·∀ τ1')⟩))
        )
        → cif-base Δ d
    CIFBCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ]
        ((d == d' ⟨ ⦇-⦈ ⇒ b ⟩) ×
         (Δ , ∅ , ~∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-base Δ d
    CIFBFailedCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d' ⟨ τ' ⇒⦇-⦈⇏ b ⟩) ×
         (Δ , ∅ , ~∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (τ' ≠ b)
        )
       → cif-base Δ d

  canonical-indeterminate-forms-base : ∀{Δ d} →
                                       Δ , ∅ , ~∅ ⊢ d :: b →
                                       d indet →
                                       cif-base Δ d
--  canonical-indeterminate-forms-base TAConst ()
  canonical-indeterminate-forms-base (TAVar x₁) ()
  canonical-indeterminate-forms-base (TAAp wt wt₁) (IAp x ind x₁) = CIFBAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-base (TATAp {τ2 = b} x x₁ x₂) (ITAp x₃ ind) = CIFBTApBase (_ , _ , refl , x , ind , x₃)
  canonical-indeterminate-forms-base {d = d} (TATAp {τ1 = τ1} {τ2 = T Z} x x₁ x₂) (ITAp x₃ ind) rewrite x₂ = CIFBTApId (_ , τ1 , refl , x , ind , x₃)
  canonical-indeterminate-forms-base (TAEHole x x₁) IEHole = CIFBEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-base (TANEHole x wt x₁) (INEHole x₂) = CIFBNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-base (TACast wt x) (ICastHoleGround x₁ ind x₂) = CIFBCast (_ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-base (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) = CIFBFailedCast (_ , _ , refl , x , x₅ , x₇)

  -- -- this type gives somewhat nicer syntax for the output of the canonical
  -- -- forms lemma for indeterminates at arrow type
  -- data cif-arr : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
  --   CIFAEHole : ∀{d Δ τ1 τ2} →
  --     Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
  --       ((d == ⦇-⦈⟨ u , σ ⟩) ×
  --        ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
  --        (Δ , ∅ , ~∅ ⊢ σ :s: Γ)
  --       )
  --     → cif-arr Δ d τ1 τ2
  --   CIFANEHole : ∀{d Δ τ1 τ2} →
  --     Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
  --       ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
  --        (Δ , ∅ , ~∅ ⊢ d' :: τ') ×
  --        (d' final) ×
  --        ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
  --        (Δ , ∅ , ~∅ ⊢ σ :s: Γ)
  --       )
  --       → cif-arr Δ d τ1 τ2
  --   CIFAAp : ∀{d Δ τ1 τ2} →
  --     Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2' ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
  --       ((d == d1 ∘ d2) ×
  --        (Δ , ∅ , ~∅ ⊢ d1 :: τ2' ==> (τ1 ==> τ2)) ×
  --        (Δ , ∅ , ~∅ ⊢ d2 :: τ2') ×
  --        (d1 indet) ×
  --        (d2 final) ×
  --        ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
  --       )
  --       → cif-arr Δ d τ1 τ2
  --   CIFACast : ∀{d Δ τ1 τ2} →
  --     Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
  --       ((d == d' ⟨ (τ1' ==> τ2') ⇒ (τ1 ==> τ2) ⟩) ×
  --         (Δ , ∅ , ~∅ ⊢ d' :: τ1' ==> τ2') ×
  --         (d' indet) ×
  --         ((τ1' ==> τ2') ≠ (τ1 ==> τ2))
  --       )
  --      → cif-arr Δ d τ1 τ2
  --   CIFACastHole : ∀{d Δ τ1 τ2} →
  --     Σ[ d' ∈ ihexp ]
  --       ((d == (d' ⟨ ⦇-⦈ ⇒ ⦇-⦈ ==> ⦇-⦈ ⟩)) ×
  --        (τ1 == ⦇-⦈) ×
  --        (τ2 == ⦇-⦈) ×
  --        (Δ , ∅ , ~∅ ⊢ d' :: ⦇-⦈) ×
  --        (d' indet) ×
  --        ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
  --       )
  --       → cif-arr Δ d τ1 τ2
  --   CIFAFailedCast : ∀{d Δ τ1 τ2} →
  --     Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
  --         ((d == (d' ⟨ τ' ⇒⦇-⦈⇏ ⦇-⦈ ==> ⦇-⦈ ⟩) ) ×
  --          (τ1 == ⦇-⦈) ×
  --          (τ2 == ⦇-⦈) ×
  --          (Δ , ∅ , ~∅ ⊢ d' :: τ') ×
  --          (τ' ground) ×
  --          (τ' ≠ (⦇-⦈ ==> ⦇-⦈))
  --          )
  --         → cif-arr Δ d τ1 τ2

  -- canonical-indeterminate-forms-arr : ∀{Δ d τ1 τ2 } →
  --                                      Δ , ∅ , ~∅ ⊢ d :: (τ1 ==> τ2) →
  --                                      d indet →
  --                                      cif-arr Δ d τ1 τ2
  -- canonical-indeterminate-forms-arr (TAVar x₁) ()
  -- canonical-indeterminate-forms-arr (TALam _ wt) ()
  -- canonical-indeterminate-forms-arr (TAAp wt wt₁) (IAp x ind x₁) = CIFAAp (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  -- canonical-indeterminate-forms-arr (TAEHole x x₁) IEHole = CIFAEHole (_ , _ , _ , refl , x , x₁)
  -- canonical-indeterminate-forms-arr (TANEHole x wt x₁) (INEHole x₂) = CIFANEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  -- canonical-indeterminate-forms-arr (TACast wt x) (ICastArr x₁ ind) = CIFACast (_ , _ , _ , _ , _ , refl , wt , ind , x₁)
  -- canonical-indeterminate-forms-arr (TACast wt TCHole2) (ICastHoleGround x₁ ind GArr) = CIFACastHole (_ , refl , refl , refl , wt , ind , x₁)
  -- canonical-indeterminate-forms-arr (TAFailedCast x x₁ GArr x₃) (IFailedCast x₄ x₅ GArr x₇) = CIFAFailedCast (_ , _ , refl , refl , refl , x , x₅ , x₇)


  -- -- this type gives somewhat nicer syntax for the output of the canonical
  -- -- forms lemma for indeterminates at hole type
  -- data cif-hole : (Δ : hctx) (d : ihexp) → Set where
  --   CIFHEHole : ∀ {Δ d} →
  --     Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
  --       ((d == ⦇-⦈⟨ u , σ ⟩) ×
  --        ((u :: ⦇-⦈ [ Γ ]) ∈ Δ) ×
  --        (Δ , ∅ , ~∅ ⊢ σ :s: Γ)
  --       )
  --     → cif-hole Δ d
  --   CIFHNEHole : ∀ {Δ d} →
  --     Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
  --       ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
  --        (Δ , ∅ , ~∅ ⊢ d' :: τ') ×
  --        (d' final) ×
  --        ((u :: ⦇-⦈ [ Γ ]) ∈ Δ) ×
  --        (Δ , ∅ , ~∅ ⊢ σ :s: Γ)
  --       )
  --     → cif-hole Δ d
  --   CIFHAp : ∀ {Δ d} →
  --     Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
  --       ((d == d1 ∘ d2) ×
  --        (Δ , ∅ , ~∅ ⊢ d1 :: (τ2 ==> ⦇-⦈)) ×
  --        (Δ , ∅ , ~∅ ⊢ d2 :: τ2) ×
  --        (d1 indet) ×
  --        (d2 final) ×
  --        ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
  --       )
  --     → cif-hole Δ d
  --   CIFHCast : ∀ {Δ d} →
  --     Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
  --       ((d == d' ⟨ τ' ⇒ ⦇-⦈ ⟩) ×
  --        (Δ , ∅ , ~∅ ⊢ d' :: τ') ×
  --        (τ' ground) ×
  --        (d' indet)
  --       )
  --     → cif-hole Δ d

  -- canonical-indeterminate-forms-hole : ∀{Δ d} →
  --                                      Δ , ∅ , ~∅ ⊢ d :: ⦇-⦈ →
  --                                      d indet →
  --                                      cif-hole Δ d
  -- canonical-indeterminate-forms-hole (TAVar x₁) ()
  -- canonical-indeterminate-forms-hole (TAAp wt wt₁) (IAp x ind x₁) = CIFHAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  -- canonical-indeterminate-forms-hole (TAEHole x x₁) IEHole = CIFHEHole (_ , _ , _ , refl , x , x₁)
  -- canonical-indeterminate-forms-hole (TANEHole x wt x₁) (INEHole x₂) = CIFHNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  -- canonical-indeterminate-forms-hole (TACast wt x) (ICastGroundHole x₁ ind) = CIFHCast (_ , _ , refl , wt , x₁ , ind)
  -- canonical-indeterminate-forms-hole (TACast wt x) (ICastHoleGround x₁ ind ())
  -- canonical-indeterminate-forms-hole (TAFailedCast x x₁ () x₃) (IFailedCast x₄ x₅ x₆ x₇)

  -- canonical-indeterminate-forms-coverage : ∀{Δ d τ} →
  --                                          Δ , ∅ , ~∅ ⊢ d :: τ →
  --                                          d indet →
  --                                          τ ≠ b →
  --                                          ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
  --                                          τ ≠ ⦇-⦈ →
  --                                          ⊥
  -- canonical-indeterminate-forms-coverage TAConst () nb na nh
  -- canonical-indeterminate-forms-coverage (TAVar x₁) () nb na nh
  -- canonical-indeterminate-forms-coverage (TALam _ wt) () nb na nh
  -- canonical-indeterminate-forms-coverage {τ = b} (TAAp wt wt₁) (IAp x ind x₁) nb na nh = nb refl
  -- canonical-indeterminate-forms-coverage {τ = ⦇-⦈} (TAAp wt wt₁) (IAp x ind x₁) nb na nh = nh refl
  -- canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAAp wt wt₁) (IAp x ind x₁) nb na nh = na τ τ₁ refl
  -- canonical-indeterminate-forms-coverage {τ = b} (TAEHole x x₁) IEHole nb na nh = nb refl
  -- canonical-indeterminate-forms-coverage {τ = ⦇-⦈} (TAEHole x x₁) IEHole nb na nh = nh refl
  -- canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAEHole x x₁) IEHole nb na nh = na τ τ₁ refl
  -- canonical-indeterminate-forms-coverage {τ = b} (TANEHole x wt x₁) (INEHole x₂) nb na nh = nb refl
  -- canonical-indeterminate-forms-coverage {τ = ⦇-⦈} (TANEHole x wt x₁) (INEHole x₂) nb na nh = nh refl
  -- canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TANEHole x wt x₁) (INEHole x₂) nb na nh = na τ τ₁ refl
  -- canonical-indeterminate-forms-coverage (TACast wt x) (ICastArr x₁ ind) nb na nh = na _ _ refl
  -- canonical-indeterminate-forms-coverage (TACast wt x) (ICastGroundHole x₁ ind) nb na nh = nh refl
  -- canonical-indeterminate-forms-coverage {τ = b} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh = nb refl
  -- canonical-indeterminate-forms-coverage {τ = ⦇-⦈} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh = nh refl
  -- canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh = na τ τ₁ refl
  -- canonical-indeterminate-forms-coverage {τ = b} (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) = λ z _ _₁ → z refl
  -- canonical-indeterminate-forms-coverage {τ = ⦇-⦈} (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) = λ _ _₁ z → z refl
  -- canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) = λ _ z _₁ → z τ τ₁ refl
