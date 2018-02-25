open import Nat
open import Prelude
open import core

module complete-expansion where
  complete-ta : ∀{Γ Δ d τ} → Γ gcomplete → Δ , Γ ⊢ d :: τ → d dcomplete → τ tcomplete
  complete-ta gc TAConst comp = TCBase
  complete-ta gc (TAVar x₁) DCVar = gc x₁
  complete-ta gc (TALam wt) (DCLam comp x₁) = TCArr x₁ (complete-ta gc {!wt!} {!!}) -- TCArr x₁ (complete-ta gc wt comp)
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) with complete-ta gc wt comp
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) | TCArr qq qq₁ = qq₁
  complete-ta gc (TAEHole x x₁) ()
  complete-ta gc (TANEHole x wt x₁) ()
  complete-ta gc (TACast wt x) (DCCast comp x₁ x₂) = x₂
  complete-ta gc (TAFailedCast wt x x₁ x₂) ()

  -- todo remove when you've proven typed expansion
  postulate
        typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
        typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Γ ⊢ d :: τ')
  mutual
    complete-expansion-synth : ∀{e τ Γ Δ d} →
                               Γ gcomplete →
                               e ecomplete →
                               Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                               d dcomplete
    complete-expansion-synth gc ec ESConst = DCConst
    complete-expansion-synth gc ec (ESVar x₁) = DCVar
    complete-expansion-synth gc (ECLam2 ec x₁) (ESLam x₂ exp) = {!!} -- DCLam (complete-expansion-synth gc ec exp) x₁
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp x MAHole x₂ x₃) = {!!}
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp x MAArr x₂ x₃) = {!!}
                             -- = DCAp (DCCast (complete-expansion-ana ec x₂) {!!} {!!})
                             --        (DCCast (complete-expansion-ana ec₁ x₃) {!!} {!!})
    complete-expansion-synth gc () ESEHole
    complete-expansion-synth gc () (ESNEHole exp)
    complete-expansion-synth gc (ECAsc x ec) (ESAsc x₁) = DCCast {!complete-expansion-ana!} {!!} x

    complete-expansion-ana : ∀{e τ τ' Γ Δ d} →
                             Γ gcomplete →
                             e ecomplete →
                             Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                             d dcomplete
    complete-expansion-ana gc (ECLam1 ec) (EALam x₁ x₂ exp) = {!!}
    --   with complete-expansion-ana gc ec {!!}
    -- ... | ih = DCLam ih {!!}
    complete-expansion-ana gc ec (EASubsume x x₁ x₂ x₃) = {!!} --  complete-expansion-synth ? ?
