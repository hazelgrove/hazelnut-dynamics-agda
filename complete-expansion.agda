open import Nat
open import Prelude
open import core
open import contexts

open import correspondence

module complete-expansion where
  -- todo pull this into a lemmas file once it's complete and then include that in complete preservation
  gcomp-extend : ∀{Γ τ x} → Γ gcomplete → τ tcomplete → (Γ ,, (x , τ)) gcomplete
  gcomp-extend {x = x} gc tc x₁ t x₂ with natEQ x₁ x
  gcomp-extend {Γ = Γ} gc tc x t x₃ | Inl refl with Γ x
  gcomp-extend gc tc x x₁ refl | Inl refl | Some .x₁ = {!!} -- stupid context stuff again
  gcomp-extend gc tc x t x₃ | Inl refl | None with natEQ x x
  gcomp-extend gc tc x τ refl | Inl refl | None | Inl refl = tc
  gcomp-extend gc tc x t x₃ | Inl refl | None | Inr x₁ = abort (somenotnone (! x₃))
  gcomp-extend {Γ = Γ} gc tc x₁ t x₃ | Inr x₂ with Γ x₁
  gcomp-extend gc tc x₁ t x₄ | Inr x₃ | Some x = {!tc!} -- ditto
  gcomp-extend {x = x} gc tc x₁ t x₃ | Inr x₂ | None with natEQ x x₁
  gcomp-extend gc tc x t refl | Inr x₃ | None | Inl refl = tc
  gcomp-extend gc tc x₁ t x₄ | Inr x₃ | None | Inr x₂ = abort (somenotnone (! x₄))

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

  synth-hole-not-comp : ∀{Γ e} →  Γ ⊢ e => ⦇⦈ → Γ gcomplete → e ecomplete → ⊥ -- this is not a strong enough IH
  synth-hole-not-comp (SAsc x) gc (ECAsc () ec)
  synth-hole-not-comp (SVar {n = n} x) gc ec with gc n _ x
  ... | ()
  synth-hole-not-comp (SAp wt MAHole x₁) gc (ECAp ec ec₁) = synth-hole-not-comp wt gc ec
  synth-hole-not-comp (SAp wt MAArr x₁) gc (ECAp ec ec₁) = {!!}
  synth-hole-not-comp SEHole gc ()
  synth-hole-not-comp (SNEHole wt) gc ()

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
    complete-expansion-synth gc (ECLam2 ec x₁) (ESLam x₂ exp) = DCLam (complete-expansion-synth (gcomp-extend gc x₁) ec exp) x₁
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp x MAHole x₂ x₃) = abort (synth-hole-not-comp x gc ec)
    complete-expansion-synth gc (ECAp ec ec₁) (ESAp x MAArr x₂ x₃) = {!!}
    complete-expansion-synth gc () ESEHole
    complete-expansion-synth gc () (ESNEHole exp)
    complete-expansion-synth gc (ECAsc x ec) (ESAsc x₁) with complete-expansion-ana gc ec x₁
    ... | ih = DCCast ih (complete-ta gc (π2 (typed-expansion-ana x₁)) ih) x

    complete-expansion-ana : ∀{e τ τ' Γ Δ d} →
                             Γ gcomplete →
                             e ecomplete →
                             Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                             d dcomplete
    complete-expansion-ana gc (ECLam1 ec) (EALam x₁ MAHole exp) = {!!}
    complete-expansion-ana gc (ECLam1 ec) (EALam x₁ MAArr exp)
      with complete-expansion-ana (gcomp-extend gc {!!}) ec exp
    ... | ih = DCLam ih {!!}
    complete-expansion-ana gc ec (EASubsume x x₁ x₂ x₃) = complete-expansion-synth gc ec x₂
