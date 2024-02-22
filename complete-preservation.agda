{-# OPTIONS --allow-unsolved-metas #-}

open import Nat
open import Prelude
open import core
open import contexts
open import preservation

module complete-preservation where
  -- if you substitute a complete term into a complete term, the result is
  -- still complete.
  cp-subst : ∀ {x d1 d2} →
           d1 dcomplete →
           d2 dcomplete →
           ([ d2 / x ] d1) dcomplete
  cp-subst {x = y} (DCVar {x = x}) dc2 with natEQ x y
  cp-subst DCVar dc2 | Inl refl = dc2
  cp-subst DCVar dc2 | Inr x₂ = DCVar
  cp-subst DCConst dc2 = DCConst
  cp-subst {x = x} (DCLam {x = y} dc1 x₂) dc2 with natEQ y x
  cp-subst (DCLam dc1 x₃) dc2 | Inl refl = DCLam dc1 x₃
  cp-subst (DCLam dc1 x₃) dc2 | Inr x₂ = DCLam (cp-subst dc1 dc2) x₃
  cp-subst (DCAp dc1 dc2) dc3 = DCAp (cp-subst dc1 dc3) (cp-subst dc2 dc3)
  cp-subst (DCCast dc1 x₁ x₂) dc2 = DCCast (cp-subst dc1 dc2) x₁ x₂
  cp-subst {d1 = ·Λ x₁ d1} (DCTLam x₂) x = DCTLam (cp-subst x₂ x)
  cp-subst {d1 = d1 < x₁ >} (DCTAp x₂ x₃) x = DCTAp x₂ (cp-subst x₃ x)

  tcomplete-subst : ∀{τ t τ'} →
    τ tcomplete →
    τ' tcomplete →
    Typ[ τ' / t ] τ tcomplete
  tcomplete-subst TCBase tc' = TCBase
  tcomplete-subst {t = t} (TCVar {a = t'}) tc' with natEQ t t'
  ... | Inl refl = tc'
  ... | Inr neq = TCVar
  tcomplete-subst (TCArr tc tc₁) tc' = TCArr (tcomplete-subst tc tc') (tcomplete-subst tc₁ tc')
  tcomplete-subst {t = t} (TCForall {t = t'} tc) tc' with natEQ t t'
  ... | Inl refl = TCForall tc
  ... | Inr neq = TCForall (tcomplete-subst tc tc')

  cp-typsubst : ∀ {d t τ} →
           d dcomplete →
           τ tcomplete →
           (Ihexp[ τ / t ] d) dcomplete
  cp-typsubst DCVar tc = DCVar
  cp-typsubst DCConst tc = DCConst
  cp-typsubst (DCLam dc x) tc = DCLam (cp-typsubst dc tc) (tcomplete-subst x tc)
  cp-typsubst {t = t} (DCTLam {t = t'} dc) tc with natEQ t t'
  ... | Inl refl = DCTLam dc
  ... | Inr neq = DCTLam (cp-typsubst dc tc)
  cp-typsubst (DCAp dc dc₁) tc = DCAp (cp-typsubst dc tc) (cp-typsubst dc₁ tc)
  cp-typsubst (DCTAp x dc) tc = DCTAp (tcomplete-subst x tc) (cp-typsubst dc tc)
  cp-typsubst (DCCast dc x x₁) tc = DCCast (cp-typsubst dc tc) (tcomplete-subst x tc) (tcomplete-subst x₁ tc)

  -- this just lets me pull the particular x out of a derivation; it's not
  -- bound in any of the constructors explicitly since it's only in the
  -- lambda case; so below i have no idea how else to get a name for it,
  -- instead of leaving it dotted in the context
  lem-proj : {x : Nat} {d : ihexp} { τ : htyp} → (·λ_[_]_ x τ d) dcomplete → Σ[ y ∈ Nat ] (y == x)
  lem-proj {x} (DCLam dc x₁) = x , refl

  -- a complete well typed term steps to a complete term.
  cp-rhs : ∀{d τ d' Δ} →
             d dcomplete →
             Δ , ∅ , ∅ ⊢ d :: τ →
             d ↦ d' →
             d' dcomplete
  cp-rhs dc TAConst (Step FHOuter () FHOuter)
  cp-rhs dc (TAVar x₁) (Step FHOuter () x₃)
  cp-rhs dc (TALam _ _ wt) (Step FHOuter () FHOuter)
  -- this case is a little more complicated than it feels like it ought to
  -- be, just from horsing around with agda implicit variables.
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁ alpha) (Step FHOuter ITLam FHOuter) with lem-proj dc
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁ alpha) (Step FHOuter ITLam FHOuter) | x , refl with cp-subst {x = x} dc dc₁
  ... | qq with natEQ x x
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁ alpha) (Step FHOuter ITLam FHOuter) | x , refl | DCLam qq x₁ | Inl refl = cp-subst qq dc₁
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁ alpha) (Step FHOuter ITLam FHOuter) | x , refl | qq | Inr x₁ = abort (x₁ refl)
  cp-rhs (DCAp (DCCast dc (TCArr x x₁) (TCArr x₂ x₃)) dc₁) (TAAp (TACast wt wf x₄ alpha) wt₁ alpha') (Step FHOuter ITApCast FHOuter) = DCCast (DCAp dc (DCCast dc₁ x₂ x)) x₁ x₃
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁ alpha) (Step (FHAp1 x) x₁ (FHAp1 x₂)) = DCAp (cp-rhs dc wt (Step x x₁ x₂)) dc₁
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁ alpha) (Step (FHAp2 x) x₁ (FHAp2 x₂)) = DCAp dc (cp-rhs dc₁ wt₁ (Step x x₁ x₂))
  cp-rhs () (TAEHole x x₁ eq1 eq2) stp
  cp-rhs () (TANEHole x wt x₁ _ _) stp
  cp-rhs (DCCast dc x x₁) (TACast wt x₂ _ _) (Step FHOuter (ITCastID alpha) FHOuter) = dc
  cp-rhs (DCCast dc () x₁) (TACast wt x₂ _ _) (Step FHOuter (ITCastSucceed g1 g2 alpha) FHOuter)
  cp-rhs (DCCast dc () x₁) (TACast wt x₂ _ _) (Step FHOuter (ITCastFail x₃ x₄ x₅) FHOuter)
  cp-rhs (DCCast dc x ()) (TACast wt x₂ _ _) (Step FHOuter (ITGround x₃) FHOuter)
  cp-rhs (DCCast dc () x₁) (TACast wt x₂ _ _) (Step FHOuter (ITExpand x₃) FHOuter)
  cp-rhs (DCCast dc x x₁) (TACast wt x₂ _ _) (Step (FHCast x₃) x₄ (FHCast x₅)) = DCCast (cp-rhs dc wt (Step x₃ x₄ x₅)) x x₁
  cp-rhs () (TAFailedCast wt x x₁ x₂ alpha) stp
  cp-rhs (DCTAp tc (DCTLam dc)) (TATAp x₁ x₂ x₃) (Step FHOuter ITTLam FHOuter) = cp-typsubst dc tc
  cp-rhs (DCTAp tc (DCCast dc (TCForall tc1) (TCForall tc2))) (TATAp x₁ x₂ x₃) (Step FHOuter ITTApCast FHOuter) = DCCast (DCTAp tc dc) (tcomplete-subst tc1 tc) (tcomplete-subst tc2 tc)
  cp-rhs (DCTAp x x₅) (TATAp x₁ wt x₆) (Step (FHTAp x₂) x₃ (FHTAp x₄)) = DCTAp x (cp-rhs x₅ wt (Step x₂ x₃ x₄))
  cp-rhs (DCTLam x) wt (Step FHOuter () x₅)

  ectx-disjoint : ∀{d} → tbinders-disjoint-Γ ∅ d
  ectx-disjoint {c} = TBDΓConst
  ectx-disjoint {X x} = TBDΓVar
  ectx-disjoint {·λ x [ x₁ ] d} = TBDΓLam ectx-disjoint (TBDΓ (λ x τ' ()))
  ectx-disjoint {·Λ x d} = TBDΓTLam ectx-disjoint (UBΓ (λ x y ()))
  ectx-disjoint {⦇-⦈⟨ x ⟩} = BDΓHole
  ectx-disjoint {⦇⌜ d ⌟⦈⟨ x ⟩} = TBDΓNEHole ectx-disjoint
  ectx-disjoint {d ∘ d₁} = TBDΓAp ectx-disjoint ectx-disjoint
  ectx-disjoint {d < x >} = TBDΓTAp ectx-disjoint (TBDΓ (λ x τ' ()))
  ectx-disjoint {d ⟨ x ⇒ x₁ ⟩} = TBDΓCast ectx-disjoint (TBDΓ (λ x τ' ())) (TBDΓ (λ x τ' ()))
  ectx-disjoint {d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} = TBDΓFailedCast ectx-disjoint (TBDΓ (λ x τ' ())) (TBDΓ (λ x τ' ()))

  -- this is the main result of this file.
  complete-preservation : ∀{d τ d' Δ} →
             binders-unique d →
             tbinders-unique d →
             tbinders-disjoint-Δ Δ d →
             Δ hctxwf →
             d dcomplete →
             Δ , ∅ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Σ[ τ' ∈ htyp ] (τ' =α τ × (Δ , ∅ , ∅ ⊢ d' :: τ') × (d' dcomplete))
  complete-preservation bd tu td hwf dc wt stp with preservation bd tu td ectx-disjoint (CCtx (λ ())) hwf wt stp
  ... | (τ' , alpha , pres) = τ' , alpha , pres , cp-rhs dc wt stp
