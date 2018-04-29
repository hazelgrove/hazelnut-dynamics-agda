open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

open import structural

module disjointness where
  mutual
    expand-new-disjoint-synth : ∀ { e u τ d Δ Γ Γ' τ'} →
                          hole-name-new e u →
                          Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                          Δ ## (■ (u , Γ' , τ'))
    expand-new-disjoint-synth HNConst ESConst = empty-disj (■ (_ , _ , _))
    expand-new-disjoint-synth (HNAsc hn) (ESAsc x) = expand-new-disjoint-ana hn x
    expand-new-disjoint-synth HNVar (ESVar x₁) = empty-disj (■ (_ , _ , _))
    expand-new-disjoint-synth (HNLam1 hn) ()
    expand-new-disjoint-synth (HNLam2 hn) (ESLam x₁ exp) = expand-new-disjoint-synth hn exp
    expand-new-disjoint-synth (HNHole x) ESEHole = disjoint-singles x
    expand-new-disjoint-synth (HNNEHole x hn) (ESNEHole x₁ exp) = disjoint-parts (expand-new-disjoint-synth hn exp) (disjoint-singles x)
    expand-new-disjoint-synth (HNAp hn hn₁) (ESAp x x₁ x₂ x₃ x₄ x₅) =
                                            disjoint-parts (expand-new-disjoint-ana hn x₄)
                                                  (expand-new-disjoint-ana hn₁ x₅)

    expand-new-disjoint-ana : ∀ { e u τ d Δ Γ Γ' τ' τ2} →
                              hole-name-new e u →
                              Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                              Δ ## (■ (u , Γ' , τ'))
    expand-new-disjoint-ana hn (EASubsume x x₁ x₂ x₃) = expand-new-disjoint-synth hn x₂
    expand-new-disjoint-ana (HNLam1 hn) (EALam x₁ x₂ ex) = expand-new-disjoint-ana hn ex
    expand-new-disjoint-ana (HNHole x) EAEHole = disjoint-singles x
    expand-new-disjoint-ana (HNNEHole x hn) (EANEHole x₁ x₂) = disjoint-parts (expand-new-disjoint-synth hn x₂) (disjoint-singles x)

  mutual
    expand-disjoint-new-synth : ∀{ e τ d Δ u Γ Γ' τ'} →
                                Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                                Δ ## (■ (u , Γ' , τ')) →
                                hole-name-new e u
    expand-disjoint-new-synth ESConst disj = HNConst
    expand-disjoint-new-synth (ESVar x₁) disj = HNVar
    expand-disjoint-new-synth (ESLam x₁ ex) disj = HNLam2 (expand-disjoint-new-synth ex disj)
    expand-disjoint-new-synth (ESAp {Δ1 = Δ1} x x₁ x₂ x₃ x₄ x₅) disj
      with expand-disjoint-new-ana x₄ (disjoint-union1 disj) | expand-disjoint-new-ana x₅ (disjoint-union2 {Γ1 = Δ1} disj)
    ... | ih1 | ih2 = HNAp ih1 ih2
    expand-disjoint-new-synth {Γ = Γ} ESEHole disj = HNHole (singles-notequal disj)
    expand-disjoint-new-synth (ESNEHole {Δ = Δ} x ex) disj = HNNEHole (singles-notequal (disjoint-union2 {Γ1 = Δ} disj))
                                                                      (expand-disjoint-new-synth ex (disjoint-union1 disj))
    expand-disjoint-new-synth (ESAsc x) disj = HNAsc (expand-disjoint-new-ana x disj)

    expand-disjoint-new-ana : ∀{ e τ d Δ u Γ Γ' τ2 τ'} →
                                Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                                Δ ## (■ (u , Γ' , τ')) →
                                hole-name-new e u
    expand-disjoint-new-ana (EALam x₁ x₂ ex) disj = HNLam1 (expand-disjoint-new-ana ex disj)
    expand-disjoint-new-ana (EASubsume x x₁ x₂ x₃) disj = expand-disjoint-new-synth x₂ disj
    expand-disjoint-new-ana EAEHole disj = HNHole (singles-notequal disj)
    expand-disjoint-new-ana (EANEHole {Δ = Δ} x x₁) disj = HNNEHole (singles-notequal (disjoint-union2 {Γ1 = Δ} disj))
                                                                    (expand-disjoint-new-synth x₁ (disjoint-union1 disj))


  mutual
    -- this looks good but may not *quite* work because of the
    -- weakening calls in the two lambda cases
    expand-ana-disjoint : ∀{ e1 e2 τ1 τ2 e1' e2' τ1' τ2' Γ Δ1 Δ2 } →
          holes-disjoint e1 e2 →
          Γ ⊢ e1 ⇐ τ1 ~> e1' :: τ1' ⊣ Δ1 →
          Γ ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
          Δ1 ## Δ2
    expand-ana-disjoint hd (EASubsume x x₁ x₂ x₃) E2 = expand-synth-disjoint hd x₂ E2
    expand-ana-disjoint (HDLam1 hd) (EALam x₁ x₂ ex1) E2 = expand-ana-disjoint hd ex1 (weaken-ana-expand x₁ E2)
    expand-ana-disjoint (HDHole x) EAEHole E2 = ##-comm (expand-new-disjoint-ana x E2)
    expand-ana-disjoint (HDNEHole x hd) (EANEHole x₁ x₂) E2 = disjoint-parts (expand-synth-disjoint hd x₂ E2) (##-comm (expand-new-disjoint-ana x E2))

    expand-synth-disjoint : ∀{ e1 e2 τ1 τ2 e1' e2' τ2' Γ Δ1 Δ2 } →
          holes-disjoint e1 e2 →
          Γ ⊢ e1 ⇒ τ1 ~> e1' ⊣ Δ1 →
          Γ ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
          Δ1 ## Δ2
    expand-synth-disjoint HDConst ESConst ana = empty-disj _
    expand-synth-disjoint (HDAsc hd) (ESAsc x) ana = expand-ana-disjoint hd x ana
    expand-synth-disjoint HDVar (ESVar x₁) ana = empty-disj _
    expand-synth-disjoint (HDLam1 hd) () ana
    expand-synth-disjoint (HDLam2 hd) (ESLam x₁ synth) ana = expand-synth-disjoint hd synth (weaken-ana-expand x₁ ana)
    expand-synth-disjoint (HDHole x) ESEHole ana = ##-comm (expand-new-disjoint-ana x ana)
    expand-synth-disjoint (HDNEHole x hd) (ESNEHole x₁ synth) ana = disjoint-parts (expand-synth-disjoint hd synth ana) (##-comm (expand-new-disjoint-ana x ana))
    expand-synth-disjoint (HDAp hd hd₁) (ESAp x x₁ x₂ x₃ x₄ x₅) ana = disjoint-parts (expand-ana-disjoint hd x₄ ana) (expand-ana-disjoint hd₁ x₅ ana)
