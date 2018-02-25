open import Nat
open import Prelude
open import List
open import core
open import contexts

module complete-preservation where
  -- TODO: convert this into a module imports once proven
  postulate
      preservation : {Δ : hctx} {d d' : dhexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ

  cp-subst : ∀ {x d1 d2} →
           d1 dcomplete →
           d2 dcomplete →
           ([ d2 / x ] d1) dcomplete
  cp-subst {x = y} (DCVar {x = x}) dc2 with natEQ x y
  cp-subst DCVar dc2 | Inl refl = dc2
  cp-subst DCVar dc2 | Inr x₂ = DCVar
  cp-subst DCConst dc2 = DCConst
  cp-subst (DCLam dc1 x₂) dc2 = DCLam (cp-subst dc1 dc2) x₂
  cp-subst (DCAp dc1 dc2) dc3 = DCAp (cp-subst dc1 dc3) (cp-subst dc2 dc3)
  cp-subst (DCCast dc1 x₁ x₂) dc2 = DCCast (cp-subst dc1 dc2) x₁ x₂

  cp-rhs : ∀{d τ d' Δ} →
             d dcomplete →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             d' dcomplete
  cp-rhs dc TAConst (Step FHOuter () FHOuter)
  cp-rhs dc (TAVar x₁) stp = abort (somenotnone (! x₁))
  cp-rhs dc (TALam wt) (Step FHOuter () FHOuter)
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step FHOuter ITLam FHOuter) with cp-subst dc dc₁
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step FHOuter ITLam FHOuter) | DCLam qq x₁ = qq
  cp-rhs (DCAp (DCCast dc (TCArr x x₁) (TCArr x₂ x₃)) dc₁) (TAAp (TACast wt x₄) wt₁) (Step FHOuter ITApCast FHOuter) = DCCast (DCAp dc (DCCast dc₁ x₂ x)) x₁ x₃
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step (FHAp1 x) x₁ (FHAp1 x₂)) = DCAp (cp-rhs dc wt (Step x x₁ x₂)) dc₁
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step (FHAp2 x) x₁ (FHAp2 x₂)) = DCAp dc (cp-rhs dc₁ wt₁ (Step x x₁ x₂))
  cp-rhs () (TAEHole x x₁) stp
  cp-rhs () (TANEHole x wt x₁) stp
  cp-rhs (DCCast dc x x₁) (TACast wt x₂) (Step FHOuter ITCastID FHOuter) = dc
  cp-rhs (DCCast dc () x₁) (TACast wt x₂) (Step FHOuter (ITCastSucceed x₃) FHOuter)
  cp-rhs (DCCast dc () x₁) (TACast wt x₂) (Step FHOuter (ITCastFail x₃ x₄ x₅) FHOuter)
  cp-rhs (DCCast dc x ()) (TACast wt x₂) (Step FHOuter (ITGround x₃) FHOuter)
  cp-rhs (DCCast dc () x₁) (TACast wt x₂) (Step FHOuter (ITExpand x₃) FHOuter)
  cp-rhs (DCCast dc x x₁) (TACast wt x₂) (Step (FHCast x₃) x₄ (FHCast x₅)) = DCCast (cp-rhs dc wt (Step x₃ x₄ x₅)) x x₁
  cp-rhs () (TAFailedCast wt x x₁ x₂) stp

  complete-preservation : ∀{d τ d' Δ} →
             d dcomplete →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             (Δ , ∅ ⊢ d' :: τ) × (d' dcomplete)
  complete-preservation dc wt stp = preservation wt stp , cp-rhs dc wt stp
