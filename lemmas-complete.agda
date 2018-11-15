open import Nat
open import Prelude
open import core

open import lemmas-gcomplete

module lemmas-complete where
  -- no term is both complete and indeterminate
  lem-ind-comp : ∀{d} → d dcomplete → d indet → ⊥
  lem-ind-comp DCVar ()
  lem-ind-comp DCConst ()
  lem-ind-comp (DCLam comp x₁) ()
  lem-ind-comp (DCAp comp comp₁) (IAp x ind x₁) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastArr x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastGroundHole x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastHoleGround x₂ ind x₃) = lem-ind-comp comp ind

  -- complete types that are consistent are equal
  complete-consistency : ∀{τ1 τ2} → τ1 ~ τ2 → τ1 tcomplete → τ2 tcomplete → τ1 == τ2
  complete-consistency TCRefl TCBase comp2 = refl
  complete-consistency TCRefl (TCArr comp1 comp2) comp3 = refl
  complete-consistency TCHole1 comp1 ()
  complete-consistency TCHole2 () comp2
  complete-consistency (TCArr consis consis₁) (TCArr comp1 comp2) (TCArr comp3 comp4)
   with complete-consistency consis comp1 comp3 | complete-consistency consis₁ comp2 comp4
  ... | refl | refl = refl

  -- a well typed complete term is assigned a complete type
  complete-ta : ∀{Γ Δ d τ} → (Γ gcomplete) →
                             (Δ , Γ ⊢ d :: τ) →
                             d dcomplete →
                             τ tcomplete
  complete-ta gc TAConst comp = TCBase
  complete-ta gc (TAVar x₁) DCVar = gc _ _ x₁
  complete-ta gc (TALam a wt) (DCLam comp x₁) = TCArr x₁ (complete-ta (gcomp-extend gc x₁ a ) wt comp)
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) with complete-ta gc wt comp
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) | TCArr qq qq₁ = qq₁
  complete-ta gc (TAEHole x x₁) ()
  complete-ta gc (TANEHole x wt x₁) ()
  complete-ta gc (TACast wt x) (DCCast comp x₁ x₂) = x₂
  complete-ta gc (TAFailedCast wt x x₁ x₂) ()

  -- a well typed term synthesizes a complete type
  comp-synth : ∀{Γ e τ} →
                   Γ gcomplete →
                   e ecomplete →
                   Γ ⊢ e => τ →
                   τ tcomplete
  comp-synth gc ec SConst = TCBase
  comp-synth gc (ECAsc x ec) (SAsc x₁) = x
  comp-synth gc ec (SVar x) = gc _ _ x
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAHole x₁) with comp-synth gc ec wt
  ... | ()
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) with comp-synth gc ec wt
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) | TCArr qq qq₁ = qq₁
  comp-synth gc () SEHole
  comp-synth gc () (SNEHole _ wt)
  comp-synth gc (ECLam2 ec x₁) (SLam x₂ wt) = TCArr x₁ (comp-synth (gcomp-extend gc x₁ x₂) ec wt)
