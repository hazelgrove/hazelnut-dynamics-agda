open import Nat
open import Prelude
open import core
open import contexts
open import typed-expansion
open import lemmas-gcomplete
open import lemmas-complete

module complete-expansion where
  mutual
    complete-expansion-synth : ∀{e τ Γ Δ d} →
                               Γ gcomplete →
                               e ecomplete →
                               Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                               (d dcomplete × τ tcomplete × Δ == ∅)
    complete-expansion-synth gc ec ESConst = DCConst , TCBase , refl
    complete-expansion-synth gc ec (ESVar x₁) = DCVar , gc _ _ x₁ , refl
    complete-expansion-synth gc (ECLam2 ec x₁) (ESLam x₂ exp)
      with complete-expansion-synth (gcomp-extend gc x₁ x₂) ec exp
    ... | ih1 , ih2 , ih3 = DCLam ih1 x₁ , TCArr x₁ ih2 , ih3
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp _ _ x MAHole x₂ x₃)
      with comp-synth gc ec x
    ... | ()
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp {Δ1 = Δ1} {Δ2 = Δ2} _ _ x MAArr x₂ x₃)
      with comp-synth gc ec x
    ... | TCArr t1 t2
      with complete-expansion-ana gc ec (TCArr t1 t2) x₂ | complete-expansion-ana gc ec₁ t1 x₃
    ... | ih1 , _ ,  ih4 | ih2 , _ , ih3 = DCAp (DCCast ih1 (comp-ana gc x₂ ih1) (TCArr t1 t2)) (DCCast ih2 (comp-ana gc x₃ ih2) t1) ,
                                  t2 ,
                                  tr (λ qq → (qq ∪ Δ2) == ∅) (! ih4) (tr (λ qq → (∅ ∪ qq) == ∅) (! ih3) refl)
    complete-expansion-synth gc () ESEHole
    complete-expansion-synth gc () (ESNEHole _ exp)
    complete-expansion-synth gc (ECAsc x ec) (ESAsc x₁)
      with complete-expansion-ana gc ec x x₁
    ... | ih1 , _ , ih2 = DCCast ih1 (comp-ana gc x₁ ih1) x , x , ih2

    complete-expansion-ana : ∀{e τ τ' Γ Δ d} →
                             Γ gcomplete →
                             e ecomplete →
                             τ tcomplete →
                             Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                             (d dcomplete × τ' tcomplete × Δ == ∅)
    complete-expansion-ana gc (ECLam1 ec) () (EALam x₁ MAHole exp)
    complete-expansion-ana gc (ECLam1 ec) (TCArr t1 t2)  (EALam x₁ MAArr exp)
      with complete-expansion-ana (gcomp-extend gc t1 x₁) ec t2 exp
    ... | ih , ih3 , ih2 = DCLam ih t1 , TCArr t1 ih3 , ih2
    complete-expansion-ana gc ec tc (EASubsume x x₁ x₂ x₃)
      with complete-expansion-synth gc ec x₂
    ... | ih1 , ih2 , ih3 = ih1 , ih2 , ih3

    -- this is just a convenience since it shows up a few times above
    comp-ana : ∀{Γ e τ d τ' Δ} →
       Γ gcomplete →
       Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
       d dcomplete →
       τ' tcomplete
    comp-ana gc ex dc = complete-ta gc (π2 (typed-expansion-ana ex)) dc
