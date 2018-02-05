open import Nat
open import Prelude
open import contexts
open import core
open import type-assignment-unicity

module canonical-indeterminate-forms where
  canonical-indeterminate-forms-base : ∀{Δ d} →
                                       Δ , ∅ ⊢ d :: b →
                                       d indet →
                                       (Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ Γ' ∈ tctx ]
                                         ((d == ⦇⦈⟨ u , σ ⟩) ×
                                          ((u ::[ Γ' ] b) ∈ Δ))) +
                                       (Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ Γ' ∈ tctx ] Σ[ d' ∈ dhexp ] Σ[ τ' ∈ htyp ]
                                         ((d == ⦇ d' ⦈⟨ u , σ ⟩) ×
                                          (d' final) ×
                                          (Δ , ∅ ⊢ d' :: τ') ×
                                          ((u ::[ Γ' ] b) ∈ Δ))) +
                                       Σ[ d1 ∈ dhexp ] Σ[ d2 ∈ dhexp ] Σ[ τ2 ∈ htyp ]
                                         ((d == d1 ∘ d2) ×
                                          (Δ , ∅ ⊢ d1 :: τ2 ==> b) ×
                                          (Δ , ∅ ⊢ d2 :: τ2) ×
                                          (d1 indet) ×
                                          (d2 final) ×
                                          ((τ1 τ2 τ3 τ4 : htyp) (d1' : dhexp) → d1 ≠ (d1' ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩)))
                                         +
                                       (Σ[ d' ∈ dhexp ]
                                         ((d == d' ⟨ ⦇⦈ ⇒ b ⟩) ×
                                          (d' indet) ×
                                          ((d'' : dhexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇⦈ ⟩))))
  canonical-indeterminate-forms-base TAConst ()
  canonical-indeterminate-forms-base (TAVar x₁) ()
  canonical-indeterminate-forms-base (TAAp wt wt₁) (IAp x ind x₁) = Inr (Inr (Inl (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)))
  canonical-indeterminate-forms-base (TAEHole x x₁) IEHole = Inl (_ , _ , _ , refl , x)
  canonical-indeterminate-forms-base (TANEHole x wt x₁) (INEHole x₂) = Inr (Inl (_ , _ , _ , _ , _ , refl , x₂ , wt , x))
  canonical-indeterminate-forms-base (TACast wt x) (ICastHoleGround x₁ ind x₂) = Inr (Inr (Inr (_ , refl , ind , x₁)))

  canonical-indeterminate-forms-arr : ∀{Δ d τ1 τ2 } →
                                       Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                                       d indet →
                                       ((Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ Γ' ∈ tctx ]
                                         ((d == ⦇⦈⟨ u , σ ⟩) ×
                                          ((u ::[ Γ' ] (τ1 ==> τ2)) ∈ Δ))) +
                                        (Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ d' ∈ dhexp ] Σ[ τ' ∈ htyp ] Σ[ Γ' ∈ tctx ]
                                         ((d == ⦇ d' ⦈⟨ u , σ ⟩) ×
                                          (d' final) ×
                                          (Δ , ∅ ⊢ d' :: τ') ×
                                          ((u ::[ Γ' ] (τ1 ==> τ2)) ∈ Δ))) +
                                        (Σ[ d1 ∈ dhexp ] Σ[ d2 ∈ dhexp ] Σ[ τ ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
                                         ((d == d1 ∘ d2) ×
                                          (Δ , ∅ ⊢ d1 :: τ ==> (τ1' ==> τ2')) ×
                                          (Δ , ∅ ⊢ d2 :: τ) ×
                                          (d1 indet) ×
                                          (d2 final) ×
                                          ((τ1 τ2 τ3 τ4 : htyp) (d1' : dhexp) → d1 ≠ (d1' ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩)))) +
                                        (Σ[ d' ∈ dhexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ3 ∈ htyp ] Σ[ τ4 ∈ htyp ]
                                          ((d == d' ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩) ×
                                           (d' indet) ×
                                           ((τ1 ==> τ2) ≠ (τ3 ==> τ4)))) +
                                        (Σ[ d' ∈ dhexp ]
                                          ((τ1 == ⦇⦈) ×
                                           (τ2 == ⦇⦈) ×
                                           (d == (d' ⟨ ⦇⦈ ⇒ ⦇⦈ ==> ⦇⦈ ⟩)) ×
                                           (d' indet) ×
                                           ((d'' : dhexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇⦈ ⟩)))))
  canonical-indeterminate-forms-arr (TAVar x₁) ()
  canonical-indeterminate-forms-arr (TALam wt) ()
  canonical-indeterminate-forms-arr (TAAp wt wt₁) (IAp x ind x₁) = Inr (Inr (Inl (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)))
  canonical-indeterminate-forms-arr (TAEHole x x₁) IEHole = Inl (_ , _ , _ , refl , x)
  canonical-indeterminate-forms-arr (TANEHole x wt x₁) (INEHole x₂) = Inr (Inl (_ , _ , _ , _ , _ , refl , x₂ , wt , x ))
  canonical-indeterminate-forms-arr (TACast wt x) (ICastArr x₁ ind) = Inr (Inr (Inr (Inl (_ , _ , _ , _ , _ , refl , ind , x₁))))
  -- todo / cyrus: this is the only one that required pattern matching (or equivalently a lemma i didn't bother to state) on premises
  canonical-indeterminate-forms-arr (TACast wt TCHole2) (ICastHoleGround x₁ ind GHole) = Inr (Inr (Inr (Inr (_ , refl , refl , refl , ind , x₁) )))

  canonical-indeterminate-forms-hole : ∀{Δ d} →
                                       Δ , ∅ ⊢ d :: ⦇⦈ →
                                       d indet →
                                       (Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ Γ' ∈ tctx ]
                                         ((d == ⦇⦈⟨ u , σ ⟩) ×
                                          ((u ::[ Γ' ] ⦇⦈) ∈ Δ))) +
                                       (Σ[ u ∈ Nat ] Σ[ σ ∈ subst ] Σ[ d' ∈ dhexp ] Σ[ τ' ∈ htyp ] Σ[ Γ' ∈ tctx ]
                                         ((d == ⦇ d' ⦈⟨ u , σ ⟩) ×
                                          (d' final) ×
                                          (Δ , ∅ ⊢ d' :: τ') ×
                                          ((u ::[ Γ' ] ⦇⦈) ∈ Δ))) +
                                       (Σ[ d1 ∈ dhexp ] Σ[ d2 ∈ dhexp ] Σ[ τ2 ∈ htyp ]
                                         ((d == d1 ∘ d2) ×
                                          (Δ , ∅ ⊢ d1 :: (τ2 ==> ⦇⦈)) ×
                                          (Δ , ∅ ⊢ d2 :: τ2) ×
                                          (d1 indet) ×
                                          (d2 final) ×
                                          ((τ1 τ2 τ3 τ4 : htyp) (d1' : dhexp) → d1 ≠ (d1' ⟨ τ1 ==> τ2 ⇒ τ3 ==> τ4 ⟩)))) +
                                       (Σ[ d' ∈ dhexp ] Σ[ τ' ∈ htyp ]
                                         ((d == d' ⟨ τ' ⇒ ⦇⦈ ⟩) ×
                                          (τ' ground) ×
                                          (d indet))) --todo / cyrus: this is
                                                      --interesting; it's
                                                      --the only clause
                                                      --that's filled by
                                                      --multiple patterns
                                                      --below; maybe we
                                                      --could say something
                                                      --more specific?
  canonical-indeterminate-forms-hole (TAVar x₁) ()
  canonical-indeterminate-forms-hole (TAAp wt wt₁) (IAp x ind x₁) = Inr (Inr (Inl (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)))
  canonical-indeterminate-forms-hole (TAEHole x x₁) IEHole = Inl (_ , _ , _ , refl , x)
  canonical-indeterminate-forms-hole (TANEHole x wt x₁) (INEHole x₂) = Inr (Inl (_ , _ , _ , _ , _ , refl , x₂ , wt , x ))
  canonical-indeterminate-forms-hole (TACast wt x) (ICastGroundHole x₁ ind) = Inr (Inr (Inr (_ , _ , refl , x₁ , ICastGroundHole x₁ ind)))
  canonical-indeterminate-forms-hole (TACast wt x) (ICastHoleGround x₁ ind x₂) = Inr (Inr (Inr (_ , _ , refl , x₂ , ICastGroundHole x₂ ind)))

  canonical-indeterminate-forms-coverage : ∀{Δ d τ} →
                                           Δ , ∅ ⊢ d :: τ →
                                           d indet →
                                           τ ≠ b →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                           τ ≠ ⦇⦈ →
                                           ⊥
  canonical-indeterminate-forms-coverage TAConst () nb na nh
  canonical-indeterminate-forms-coverage (TAVar x₁) () nb na nh
  canonical-indeterminate-forms-coverage (TALam wt) () nb na nh
  canonical-indeterminate-forms-coverage {τ = b} (TAAp wt wt₁) (IAp x ind x₁) nb na nh = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TAAp wt wt₁) (IAp x ind x₁) nb na nh = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAAp wt wt₁) (IAp x ind x₁) nb na nh = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = b} (TAEHole x x₁) IEHole nb na nh = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TAEHole x x₁) IEHole nb na nh = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAEHole x x₁) IEHole nb na nh = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = b} (TANEHole x wt x₁) (INEHole x₂) nb na nh = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TANEHole x wt x₁) (INEHole x₂) nb na nh = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TANEHole x wt x₁) (INEHole x₂) nb na nh = na τ τ₁ refl
  canonical-indeterminate-forms-coverage (TACast wt x) (ICastArr x₁ ind) nb na nh = na _ _ refl
  canonical-indeterminate-forms-coverage (TACast wt x) (ICastGroundHole x₁ ind) nb na nh = nh refl
  canonical-indeterminate-forms-coverage {τ = b} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh = na τ τ₁ refl
