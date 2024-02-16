open import Nat
open import Prelude
open import core
open alpha

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
  lem-ind-comp {d < x₁ >} (DCTAp x₂ x₃) (ITAp x x₄) = lem-ind-comp x₃ x₄
  lem-ind-comp {d ⟨ ·∀ x x₁ ⇒ ·∀ t2 τ2 ⟩} (DCCast x₂ x₃ x₄)
    (ICastForall x₅ x₆) = lem-ind-comp x₂ x₆

  -- complete types that are consistent are alpha equivalent
  complete-consistency : ∀{τ1 τ2 ΓL ΓR} → ΓL , ΓR ⊢ τ1 ~ τ2 → τ1 tcomplete → τ2 tcomplete → ΓL , ΓR ⊢ τ1 =α τ2
  complete-consistency ConsistBase TCBase TCBase = AlphaBase
  complete-consistency (ConsistVarFree x x₁) TCVar TCVar = AlphaVarFree x x₁
  complete-consistency (ConsistVarBound x x₁) TCVar TCVar = AlphaVarBound x x₁
  complete-consistency ConsistHole1 TCBase ()
  complete-consistency ConsistHole1 TCVar ()
  complete-consistency ConsistHole1 (TCArr tc1 tc2) ()
  complete-consistency ConsistHole1 (TCForall tc1) ()
  complete-consistency ConsistHole2 () tc2
  complete-consistency (ConsistArr consis consis₁) (TCArr tc1 tc2) (TCArr tc3 tc4) = AlphaArr (complete-consistency consis tc1 tc3) (complete-consistency consis₁ tc2 tc4)
  complete-consistency (ConsistForall consis) (TCForall tc1) (TCForall tc2) = AlphaForall (complete-consistency consis tc1 tc2)

  {-
  complete-consistency : ∀{τ1 τ2} → τ1 ~ τ2 → τ1 tcomplete → τ2 tcomplete → τ1 == τ2
  complete-consistency TCRefl TCBase comp2 = refl
  complete-consistency TCRefl (TCArr comp1 comp2) comp3 = refl
  complete-consistency TCHole1 comp1 ()
  complete-consistency TCHole2 () comp2
  complete-consistency (TCArr consis consis₁) (TCArr comp1 comp2) (TCArr comp3 comp4)
   with complete-consistency consis comp1 comp3 | complete-consistency consis₁ comp2 comp4
  ... | refl | refl = refl
  -}

  subst-complete : ∀{τ1 τ2 t} →
    τ1 tcomplete → τ2 tcomplete →
    Typ[ τ1 / t ] τ2 tcomplete
  subst-complete tc1 TCBase = TCBase
  subst-complete {t = t} tc1 (TCVar {a = t'}) with natEQ t t'
  ... | Inl refl = tc1
  ... | Inr neq = TCVar
  subst-complete tc1 (TCArr tc2 tc3) = TCArr (subst-complete tc1 tc2) (subst-complete tc1 tc3)
  subst-complete {t = t} tc1 (TCForall {t = t'} tc2) with natEQ t t'
  ... | Inl refl = TCForall tc2
  ... | Inr neq = TCForall (subst-complete tc1 tc2)

  -- a well typed complete term is assigned a complete type
  complete-ta : ∀{Γ Θ Δ d τ} → (Γ gcomplete) →
                             (Δ , Θ , Γ ⊢ d :: τ) →
                             d dcomplete →
                             τ tcomplete
  complete-ta gc TAConst comp = TCBase
  complete-ta gc (TAVar x₁) DCVar = gc _ _ x₁
  complete-ta gc (TALam a wf wt) (DCLam comp x₁) = TCArr x₁ (complete-ta (gcomp-extend gc x₁ a) wt comp)
  complete-ta gc (TAAp wt wt₁ alpha) (DCAp comp comp₁) with complete-ta gc wt comp
  complete-ta gc (TAAp wt wt₁ alpha) (DCAp comp comp₁) | TCArr qq qq₁ = qq₁
  complete-ta gc (TAEHole x x₁ x₂ x₃) ()
  complete-ta gc (TANEHole x wt x₁ x₂ x₃) ()
  complete-ta gc (TACast wt x x₁ x₂) (DCCast comp x₃ x₄) = x₄
  complete-ta gc (TAFailedCast wt x x₁ x₂ x₃) ()
  complete-ta x (TATLam x₂ x₃) (DCTLam x₁) = TCForall (complete-ta x x₃ x₁)
  complete-ta x (TATAp {t = t'} x₂ x₃ x₄) (DCTAp x₁ x₅) with complete-ta x x₃ x₅
  ... | TCForall tc rewrite ! x₄ = subst-complete x₁ tc

  -- a well typed term synthesizes a complete type
  comp-synth : ∀{Γ Θ e τ} →
                   Γ gcomplete →
                   e ecomplete →
                   Θ , Γ ⊢ e => τ →
                   τ tcomplete
  comp-synth gc ec SConst = TCBase
  comp-synth gc (ECAsc x ec) (SAsc x₁ _) = x
  comp-synth gc ec (SVar x) = gc _ _ x
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAHole x₁) with comp-synth gc ec wt
  ... | ()
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) with comp-synth gc ec wt
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) | TCArr qq qq₁ = qq₁
  comp-synth gc () SEHole
  comp-synth gc () (SNEHole _ wt)
  comp-synth gc (ECLam2 ec x₁) (SLam x₂ wf wt) = TCArr x₁ (comp-synth (gcomp-extend gc x₁ x₂) ec wt)
  comp-synth x (ECTLam x₁) (STLam x₂) = TCForall (comp-synth x x₁ x₂)
  comp-synth x (ECTAp x₁ x₆) (STAp {τ2 = ⦇-⦈} x₂ x₃ x₄ x₅) with comp-synth x x₆ x₃
  ... | ()
  comp-synth x (ECTAp x₁ x₄) (STAp {τ2 = ·∀ x₆ τ2} x₂ x₃ MFForall x₅) with comp-synth x x₄ x₃
  ... | TCForall tc rewrite ! x₅ = subst-complete x₁ tc
 