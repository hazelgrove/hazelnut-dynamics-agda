open import Nat
open import Prelude
open import core
open import contexts
open import typed-expansion
open import structural-assumptions

module complete-expansion where
  -- this might be derivable from things below and a fact about => and ::
  -- that we seem to have not proven
  complete-ta : ∀{Γ Δ d τ} → (Γ gcomplete) → (Δ , Γ ⊢ d :: τ) → d dcomplete → τ tcomplete
  complete-ta gc TAConst comp = TCBase
  complete-ta gc (TAVar x₁) DCVar = gc _ _ x₁
  complete-ta gc (TALam wt) (DCLam comp x₁) = TCArr x₁ (complete-ta (gcomp-extend gc x₁) wt comp)
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) with complete-ta gc wt comp
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) | TCArr qq qq₁ = qq₁
  complete-ta gc (TAEHole x x₁) ()
  complete-ta gc (TANEHole x wt x₁) ()
  complete-ta gc (TACast wt x) (DCCast comp x₁ x₂) = x₂
  complete-ta gc (TAFailedCast wt x x₁ x₂) ()

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
  comp-synth gc (ECLam2 ec x₁) (SLam x₂ wt) = TCArr x₁ (comp-synth (gcomp-extend gc x₁) ec wt)

  mutual
    complete-expansion-synth : ∀{e τ Γ Δ d} →
                               Γ gcomplete →
                               e ecomplete →
                               Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                               (d dcomplete × τ tcomplete)
    complete-expansion-synth gc ec ESConst = DCConst , TCBase
    complete-expansion-synth gc ec (ESVar x₁) = DCVar , gc _ _ x₁
    complete-expansion-synth gc (ECLam2 ec x₁) (ESLam x₂ exp) with complete-expansion-synth (gcomp-extend gc x₁) ec exp
    ... | ih1 , ih2 = DCLam ih1 x₁ , TCArr x₁ ih2
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp _ _ x MAHole x₂ x₃) with comp-synth gc ec x
    ... | ()
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp _ _ x MAArr x₂ x₃)
      with comp-synth gc ec x
    ... | TCArr t1 t2
      with complete-expansion-ana gc ec (TCArr t1 t2) x₂ | complete-expansion-ana gc ec₁ t1 x₃
    ... | ih1 | ih2 = DCAp (DCCast ih1 (comp-ana gc x₂ ih1) (TCArr t1 t2)) (DCCast ih2 (comp-ana gc x₃ ih2) t1) , t2

    complete-expansion-synth gc () ESEHole
    complete-expansion-synth gc () (ESNEHole _ exp)
    complete-expansion-synth gc (ECAsc x ec) (ESAsc x₁)
      with complete-expansion-ana gc ec x x₁
    ... | ih = DCCast ih (comp-ana gc x₁ ih) x , x

    complete-expansion-ana : ∀{e τ τ' Γ Δ d} →
                             Γ gcomplete →
                             e ecomplete →
                             τ tcomplete →
                             Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                             d dcomplete
    complete-expansion-ana gc (ECLam1 ec) () (EALam x₁ MAHole exp)
    complete-expansion-ana gc (ECLam1 ec) (TCArr t1 t2)  (EALam x₁ MAArr exp)
      with complete-expansion-ana (gcomp-extend gc t1) ec t2 exp
    ... | ih = DCLam ih t1
    complete-expansion-ana gc ec tc (EASubsume x x₁ x₂ x₃) = π1(complete-expansion-synth gc ec x₂)

    --this is just a convenience since it shows up a few times above
    comp-ana : ∀{Γ e τ d τ' Δ} →
       Γ gcomplete →
       Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
       d dcomplete →
       τ' tcomplete
    comp-ana gc ex dc = complete-ta gc (π2 (typed-expansion-ana ex)) dc
