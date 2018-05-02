open import Nat
open import Prelude
open import core
open import contexts
open import typed-expansion
open import lemmas-gcomplete

module complete-expansion where
  -- this might be derivable from things below and a fact about => and ::
  -- that we seem to have not proven
  complete-ta : ∀{Γ Δ d τ} → (Γ gcomplete) → (Δ , Γ ⊢ d :: τ) → d dcomplete → τ tcomplete
  complete-ta gc TAConst comp = TCBase
  complete-ta gc (TAVar x₁) DCVar = gc _ _ x₁
  complete-ta gc (TALam a wt) (DCLam comp x₁) = TCArr x₁ (complete-ta (gcomp-extend gc x₁ a ) wt comp)
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
  comp-synth gc (ECLam2 ec x₁) (SLam x₂ wt) = TCArr x₁ (comp-synth (gcomp-extend gc x₁ x₂) ec wt)

  mutual
    complete-expansion-synth : ∀{e τ Γ Δ d} →
                               Γ gcomplete →
                               e ecomplete →
                               Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                               (d dcomplete × τ tcomplete × Δ == ∅)
    complete-expansion-synth gc ec ESConst = DCConst , TCBase , refl
    complete-expansion-synth gc ec (ESVar x₁) = DCVar , gc _ _ x₁ , refl
    complete-expansion-synth gc (ECLam2 ec x₁) (ESLam x₂ exp) with complete-expansion-synth (gcomp-extend gc x₁ x₂) ec exp
    ... | ih1 , ih2 , ih3 = DCLam ih1 x₁ , TCArr x₁ ih2 , ih3
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp _ _ x MAHole x₂ x₃) with comp-synth gc ec x
    ... | ()
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp {Δ1 = Δ1} {Δ2 = Δ2} _ _ x MAArr x₂ x₃)
      with comp-synth gc ec x
    ... | TCArr t1 t2
      with complete-expansion-ana gc ec (TCArr t1 t2) x₂ | complete-expansion-ana gc ec₁ t1 x₃
    ... | ih1 , ih4 | ih2 , ih3 = DCAp (DCCast ih1 (comp-ana gc x₂ ih1) (TCArr t1 t2)) (DCCast ih2 (comp-ana gc x₃ ih2) t1) ,
                                  t2 ,
                                  tr (λ qq → (qq ∪ Δ2) == ∅) (! ih4) (tr (λ qq → (∅ ∪ qq) == ∅) (! ih3) refl)
    complete-expansion-synth gc () ESEHole
    complete-expansion-synth gc () (ESNEHole _ exp)
    complete-expansion-synth gc (ECAsc x ec) (ESAsc x₁)
      with complete-expansion-ana gc ec x x₁
    ... | ih1 , ih2 = DCCast ih1 (comp-ana gc x₁ ih1) x , x , ih2

    complete-expansion-ana : ∀{e τ τ' Γ Δ d} →
                             Γ gcomplete →
                             e ecomplete →
                             τ tcomplete →
                             Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                             (d dcomplete × Δ == ∅)
    complete-expansion-ana gc (ECLam1 ec) () (EALam x₁ MAHole exp)
    complete-expansion-ana gc (ECLam1 ec) (TCArr t1 t2)  (EALam x₁ MAArr exp)
      with complete-expansion-ana (gcomp-extend gc t1 x₁) ec t2 exp
    ... | ih , ih2 = DCLam ih t1 , ih2
    complete-expansion-ana gc ec tc (EASubsume x x₁ x₂ x₃)
      with complete-expansion-synth gc ec x₂
    ... | ih1 , ih2 , ih3 = ih1 , ih3

    --this is just a convenience since it shows up a few times above
    comp-ana : ∀{Γ e τ d τ' Δ} →
       Γ gcomplete →
       Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
       d dcomplete →
       τ' tcomplete
    comp-ana gc ex dc = complete-ta gc (π2 (typed-expansion-ana ex)) dc
