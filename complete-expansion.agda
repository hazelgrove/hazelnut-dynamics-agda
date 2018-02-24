open import Nat
open import Prelude
open import core

module complete-expansion where
  complete-ta : ∀{Γ Δ d τ} → Δ , Γ ⊢ d :: τ → d dcomplete → τ tcomplete
  complete-ta TAConst comp = TCBase
  complete-ta (TAVar x₁) DCVar = {!!}
  complete-ta (TALam wt) (DCLam comp x₁) = TCArr x₁ (complete-ta wt comp)
  complete-ta (TAAp wt wt₁) (DCAp comp comp₁) with complete-ta wt comp
  complete-ta (TAAp wt wt₁) (DCAp comp comp₁) | TCArr qq qq₁ = qq₁
  complete-ta (TAEHole x x₁) ()
  complete-ta (TANEHole x wt x₁) ()
  complete-ta (TACast wt x) (DCCast comp x₁ x₂) = x₂
  complete-ta (TAFailedCast wt x x₁ x₂) ()

  -- todo remove when you've proven typed expansion
  postulate
        typed-expansion-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
        typed-expansion-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          (τ' ~ τ) × (Δ , Γ ⊢ d :: τ')
  -- todo: this might make it go, or do it for closed terms only?
  _gcomplete : tctx → Set
  Γ gcomplete = (x : Nat) (t : htyp) → (Γ x) == Some t → t tcomplete

  mutual
    complete-expansion-synth : ∀{e τ Γ Δ d} →
                               e ecomplete →
                               Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                               d dcomplete
    complete-expansion-synth ec ESConst = DCConst
    complete-expansion-synth ec (ESVar x₁) = DCVar
    complete-expansion-synth (ECLam2 ec x₁) (ESLam x₂ exp) = DCLam (complete-expansion-synth ec exp) x₁
    complete-expansion-synth (ECAp ec ec₁) (ESAp x x₁ x₂ x₃) = DCAp (DCCast {!!} {!!} {!!})
                                                                    (DCCast {!!} {!!} {!!})
    complete-expansion-synth () ESEHole
    complete-expansion-synth () (ESNEHole exp)
    complete-expansion-synth (ECAsc x ec) (ESAsc x₁) = DCCast {!complete-expansion-ana!} {!!} x

    complete-expansion-ana : ∀{e τ τ' Γ Δ d} →
                             e ecomplete →
                             Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                             d dcomplete
    complete-expansion-ana (ECLam1 ec) (EALam x₁ x₂ exp)
      with complete-expansion-ana ec exp
    ... | ih = DCLam ih {!!}
    complete-expansion-ana ec (EASubsume x x₁ x₂ x₃) = complete-expansion-synth ec x₂
