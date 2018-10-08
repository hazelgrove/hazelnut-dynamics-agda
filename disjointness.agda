open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness
open import exchange
open import lemmas-freshness
open import weakening

--open import structural-assumptions

module disjointness where

  --todo move to weakening
  mutual
    weaken-synth-expand : ∀{x Γ e τ d Δ τ'} → fresh x d
                                             → Γ ⊢ e ⇒ τ ~> d ⊣ Δ
                                             → (Γ ,, (x , τ')) ⊢ e ⇒ τ ~> d ⊣ Δ
    weaken-synth-expand frsh ESConst = ESConst
    weaken-synth-expand {x = y} {Γ = Γ} {τ = τ} frsh (ESVar {x = x} x₂) = ESVar (x∈∪l Γ (■ (y , _)) x τ x₂)
    weaken-synth-expand {Γ = Γ} (FLam x₁ frsh) (ESLam x₂ syn) = ESLam (apart-extend1 Γ (flip x₁) x₂) (exchange-expand-synth {Γ = Γ} (flip x₁) (weaken-synth-expand frsh syn))
    weaken-synth-expand (FAp (FCast frsh) (FCast frsh₁)) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) = ESAp x₁ x₂ (weaken-synth (fresh-expand-ana2 frsh x₅) x₃) x₄ (weaken-ana-expand frsh x₅) (weaken-ana-expand frsh₁ x₆)
    weaken-synth-expand {x = x } {Γ = Γ} {τ' = τ'}  frsh (ESEHole {u = u})= {!ESEHole {Γ = Γ ,, (x , τ')} {u = u}  !}
    weaken-synth-expand frsh (ESNEHole x₁ syn) = {!!}
    weaken-synth-expand (FCast frsh) (ESAsc x₁) = ESAsc (weaken-ana-expand frsh x₁)

    weaken-ana-expand : ∀{ Γ e τ d τ' Δ x τ* } → fresh x d
                                                → Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
                                                → (Γ ,, (x , τ*)) ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
    weaken-ana-expand {Γ = Γ} (FLam x₁ frsh) (EALam x₂ x₃ ana) = EALam (apart-extend1 Γ (flip x₁) x₂) x₃ (exchange-expand-ana {Γ = Γ} (flip x₁) (weaken-ana-expand frsh ana))
    weaken-ana-expand frsh (EASubsume x₁ x₂ x₃ x₄) = EASubsume x₁ x₂ (weaken-synth-expand frsh x₃) x₄
    weaken-ana-expand (FHole (EFId x₁)) EAEHole = {!!}
    weaken-ana-expand (FNEHole (EFId x₁) frsh) (EANEHole x₂ x₃) = {!!}


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
    expand-ana-disjoint : ∀{ e1 e2 τ1 τ2 e1' e2' τ1' τ2' Γ Δ1 Δ2 } →
          holes-disjoint e1 e2 →
          Γ ⊢ e1 ⇐ τ1 ~> e1' :: τ1' ⊣ Δ1 →
          Γ ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
          Δ1 ## Δ2
    expand-ana-disjoint hd (EASubsume x x₁ x₂ x₃) E2 = expand-synth-disjoint hd x₂ E2
    expand-ana-disjoint (HDLam1 hd) (EALam x₁ x₂ ex1) E2 = expand-ana-disjoint hd ex1 (weaken-ana-expand {!!} E2)
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
    expand-synth-disjoint (HDLam2 hd) (ESLam x₁ synth) ana = expand-synth-disjoint hd synth (weaken-ana-expand {!!} ana)
    expand-synth-disjoint (HDHole x) ESEHole ana = ##-comm (expand-new-disjoint-ana x ana)
    expand-synth-disjoint (HDNEHole x hd) (ESNEHole x₁ synth) ana = disjoint-parts (expand-synth-disjoint hd synth ana) (##-comm (expand-new-disjoint-ana x ana))
    expand-synth-disjoint (HDAp hd hd₁) (ESAp x x₁ x₂ x₃ x₄ x₅) ana = disjoint-parts (expand-ana-disjoint hd x₄ ana) (expand-ana-disjoint hd₁ x₅ ana)


  -- these lemmas are all structurally recursive. morally, they
  -- establish the properties about reduction that would be obvious /
  -- baked into Agda if holes-disjoint was defined as a function
  -- rather than a judgement (datatype), or if we had defined all the
  -- O(n^2) cases rather than relying on a little indirection to only
  -- have O(n) cases. that work has to go somewhwere, and we prefer
  -- that it goes here.
  ds-lem-asc : ∀{e1 e2 τ} → holes-disjoint e2 e1 → holes-disjoint e2 (e1 ·: τ)
  ds-lem-asc HDConst = HDConst
  ds-lem-asc (HDAsc hd) = HDAsc (ds-lem-asc hd)
  ds-lem-asc HDVar = HDVar
  ds-lem-asc (HDLam1 hd) = HDLam1 (ds-lem-asc hd)
  ds-lem-asc (HDLam2 hd) = HDLam2 (ds-lem-asc hd)
  ds-lem-asc (HDHole x) = HDHole (HNAsc x)
  ds-lem-asc (HDNEHole x hd) = HDNEHole (HNAsc x) (ds-lem-asc hd)
  ds-lem-asc (HDAp hd hd₁) = HDAp (ds-lem-asc hd) (ds-lem-asc hd₁)

  ds-lem-lam1 : ∀{e1 e2 x} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x e1)
  ds-lem-lam1 HDConst = HDConst
  ds-lem-lam1 (HDAsc hd) = HDAsc (ds-lem-lam1 hd)
  ds-lem-lam1 HDVar = HDVar
  ds-lem-lam1 (HDLam1 hd) = HDLam1 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDLam2 hd) = HDLam2 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDHole x₁) = HDHole (HNLam1 x₁)
  ds-lem-lam1 (HDNEHole x₁ hd) = HDNEHole (HNLam1 x₁) (ds-lem-lam1 hd)
  ds-lem-lam1 (HDAp hd hd₁) = HDAp (ds-lem-lam1 hd) (ds-lem-lam1 hd₁)

  ds-lem-lam2 : ∀{e1 e2 x τ} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x [ τ ] e1)
  ds-lem-lam2 HDConst = HDConst
  ds-lem-lam2 (HDAsc hd) = HDAsc (ds-lem-lam2 hd)
  ds-lem-lam2 HDVar = HDVar
  ds-lem-lam2 (HDLam1 hd) = HDLam1 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDLam2 hd) = HDLam2 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDHole x₁) = HDHole (HNLam2 x₁)
  ds-lem-lam2 (HDNEHole x₁ hd) = HDNEHole (HNLam2 x₁) (ds-lem-lam2 hd)
  ds-lem-lam2 (HDAp hd hd₁) = HDAp (ds-lem-lam2 hd) (ds-lem-lam2 hd₁)

  ds-lem-nehole : ∀{e e1 u} → holes-disjoint e e1 → hole-name-new e u → holes-disjoint e ⦇ e1 ⦈[ u ]
  ds-lem-nehole HDConst ν = HDConst
  ds-lem-nehole (HDAsc hd) (HNAsc ν) = HDAsc (ds-lem-nehole hd ν)
  ds-lem-nehole HDVar ν = HDVar
  ds-lem-nehole (HDLam1 hd) (HNLam1 ν) = HDLam1 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDLam2 hd) (HNLam2 ν) = HDLam2 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDHole x) (HNHole x₁) = HDHole (HNNEHole (flip x₁) x)
  ds-lem-nehole (HDNEHole x hd) (HNNEHole x₁ ν) = HDNEHole (HNNEHole (flip x₁) x) (ds-lem-nehole hd ν)
  ds-lem-nehole (HDAp hd hd₁) (HNAp ν ν₁) = HDAp (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)

  ds-lem-ap : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (e1 ∘ e2)
  ds-lem-ap HDConst hd2 = HDConst
  ds-lem-ap (HDAsc hd1) (HDAsc hd2) = HDAsc (ds-lem-ap hd1 hd2)
  ds-lem-ap HDVar hd2 = HDVar
  ds-lem-ap (HDLam1 hd1) (HDLam1 hd2) = HDLam1 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDLam2 hd1) (HDLam2 hd2) = HDLam2 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDHole x) (HDHole x₁) = HDHole (HNAp x x₁)
  ds-lem-ap (HDNEHole x hd1) (HDNEHole x₁ hd2) = HDNEHole (HNAp x x₁) (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDAp hd1 hd2) (HDAp hd3 hd4) = HDAp (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)

  -- holes-disjoint is symmetric
  disjoint-sym : (e1 e2 : hexp) → holes-disjoint e1 e2 → holes-disjoint e2 e1
  disjoint-sym .c c HDConst = HDConst
  disjoint-sym .c (e2 ·: x) HDConst = HDAsc (disjoint-sym _ _ HDConst)
  disjoint-sym .c (X x) HDConst = HDVar
  disjoint-sym .c (·λ x e2) HDConst = HDLam1 (disjoint-sym c e2 HDConst)
  disjoint-sym .c (·λ x [ x₁ ] e2) HDConst = HDLam2 (disjoint-sym c e2 HDConst)
  disjoint-sym .c ⦇⦈[ x ] HDConst = HDHole HNConst
  disjoint-sym .c ⦇ e2 ⦈[ x ] HDConst = HDNEHole HNConst (disjoint-sym c e2 HDConst)
  disjoint-sym .c (e2 ∘ e3) HDConst = HDAp (disjoint-sym c e2 HDConst) (disjoint-sym c e3 HDConst)

  disjoint-sym _ c (HDAsc hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x) (HDAsc hd) | HDAsc ih = HDAsc (ds-lem-asc ih)
  disjoint-sym _ (X x) (HDAsc hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDAsc hd) | HDLam1 ih = HDLam1 (ds-lem-asc ih)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) | HDLam2 ih = HDLam2 (ds-lem-asc ih)
  disjoint-sym _ ⦇⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDAsc hd) | HDHole x₁ = HDHole (HNAsc x₁)
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDAsc hd) | HDNEHole x₁ ih = HDNEHole (HNAsc x₁) (ds-lem-asc ih)
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) | HDAp ih ih₁ = HDAp (ds-lem-asc ih) (ds-lem-asc ih₁)

  disjoint-sym _ c HDVar = HDConst
  disjoint-sym _ (e2 ·: x₁) HDVar = HDAsc (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (X x₁) HDVar = HDVar
  disjoint-sym _ (·λ x₁ e2) HDVar = HDLam1 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) HDVar = HDLam2 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ ⦇⦈[ x₁ ] HDVar = HDHole HNVar
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] HDVar = HDNEHole HNVar (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (e2 ∘ e3) HDVar = HDAp (disjoint-sym _ e2 HDVar) (disjoint-sym _ e3 HDVar)

  disjoint-sym _ c (HDLam1 hd) = HDConst
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) | HDAsc ih = HDAsc (ds-lem-lam1 ih)
  disjoint-sym _ (X x₁) (HDLam1 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) | HDLam1 ih = HDLam1 (ds-lem-lam1 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) | HDLam2 ih = HDLam2 (ds-lem-lam1 ih)
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam1 hd) | HDHole x = HDHole (HNLam1 x)
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam1 hd) | HDNEHole x ih = HDNEHole (HNLam1 x) (ds-lem-lam1 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam1 ih) (ds-lem-lam1 ih₁)

  disjoint-sym _ c (HDLam2 hd) = HDConst
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) | HDAsc ih = HDAsc (ds-lem-lam2 ih)
  disjoint-sym _ (X x₁) (HDLam2 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) | HDLam1 ih = HDLam1 (ds-lem-lam2 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) | HDLam2 ih = HDLam2 (ds-lem-lam2 ih)
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam2 hd) | HDHole x = HDHole (HNLam2 x)
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x₁ ] (HDLam2 hd) | HDNEHole x ih = HDNEHole (HNLam2 x) (ds-lem-lam2 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam2 ih) (ds-lem-lam2 ih₁)

  disjoint-sym _ c (HDHole x) = HDConst
  disjoint-sym _ (e2 ·: x) (HDHole (HNAsc x₁)) = HDAsc (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (X x) (HDHole x₁) = HDVar
  disjoint-sym _ (·λ x e2) (HDHole (HNLam1 x₁)) = HDLam1 (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDHole (HNLam2 x₂)) = HDLam2 (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₂))
  disjoint-sym _ ⦇⦈[ x ] (HDHole (HNHole x₁)) =  HDHole (HNHole (flip x₁))
  disjoint-sym _ ⦇ e2 ⦈[ u' ] (HDHole (HNNEHole x x₁)) = HDNEHole (HNHole (flip x)) (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (e2 ∘ e3) (HDHole (HNAp x x₁)) = HDAp (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x))
                                                    (disjoint-sym ⦇⦈[ _ ] e3 (HDHole x₁))

  disjoint-sym _ c (HDNEHole x hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e ·: x) (HDNEHole (HNAsc x₁) hd) | HDAsc ih = HDAsc (ds-lem-nehole ih x₁)
  disjoint-sym _ (X x) (HDNEHole x₁ hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDNEHole (HNLam1 x₁) hd) | HDLam1 ih = HDLam1 (ds-lem-nehole ih x₁)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole x₂ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole (HNLam2 x₂) hd) | HDLam2 ih = HDLam2 (ds-lem-nehole ih x₂)
  disjoint-sym _ ⦇⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDNEHole (HNHole x₂) hd) | HDHole x₁ = HDHole (HNNEHole (flip x₂) x₁)
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇ e2 ⦈[ x ] (HDNEHole (HNNEHole x₂ x₃) hd) | HDNEHole x₁ ih = HDNEHole (HNNEHole (flip x₂) x₁) (ds-lem-nehole ih x₃)
  disjoint-sym _ (e2 ∘ e3) (HDNEHole x hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e1 ∘ e3) (HDNEHole (HNAp x x₁) hd) | HDAp ih ih₁ = HDAp (ds-lem-nehole ih x) (ds-lem-nehole ih₁ x₁)

  disjoint-sym _ c (HDAp hd hd₁) = HDConst
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) | HDAsc ih | HDAsc ih1 = HDAsc (ds-lem-ap ih ih1)
  disjoint-sym _ (X x) (HDAp hd hd₁) = HDVar
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) | HDLam1 ih | HDLam1 ih1 = HDLam1 (ds-lem-ap ih ih1)
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) | HDLam2 ih | HDLam2 ih1 = HDLam2 (ds-lem-ap ih ih1)
  disjoint-sym _ ⦇⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇⦈[ x ] (HDAp hd hd₁) | HDHole x₁ | HDHole x₂ = HDHole (HNAp x₁ x₂)
  disjoint-sym _ ⦇ e3 ⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇ e3 ⦈[ x ] (HDAp hd hd₁) | HDNEHole x₁ ih | HDNEHole x₂ ih1 = HDNEHole (HNAp x₁ x₂) (ds-lem-ap ih ih1)
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) | HDAp ih ih₁ | HDAp ih1 ih2 = HDAp (ds-lem-ap ih ih1) (ds-lem-ap ih₁ ih2)


  -- note that this is false, so holes-disjoint isn't transitive
  -- disjoint-new : ∀{e1 e2 u} → holes-disjoint e1 e2 → hole-name-new e1 u → hole-name-new e2 u

  -- it's also not reflexive, because ⦇⦈[ u ] isn't hole-disjoint with
  -- itself since u == u; it's not anti-reflexive, because the
  -- expression c *is* hole-disjoint with itself (abeit vacuously)
