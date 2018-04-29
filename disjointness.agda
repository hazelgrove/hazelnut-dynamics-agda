open import Prelude
open import Nat
open import core
open import contexts

open import structural

module disjointness where
  mutual
    expand-new-disjoint-synth : ∀ { e u τ d Δ Γ τ'} →
                          hole-name-new e u →
                          Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                          Δ ## (■ (u , Γ , τ'))
    expand-new-disjoint-synth HNConst ESConst = empty-disj (■ (_ , _ , _))
    expand-new-disjoint-synth (HNAsc hn) (ESAsc x) = expand-new-disjoint-ana hn x
    expand-new-disjoint-synth HNVar (ESVar x₁) = empty-disj (■ (_ , _ , _))
    expand-new-disjoint-synth (HNLam1 hn) ()
    expand-new-disjoint-synth {τ' = τ'} (HNLam2 hn) (ESLam x₁ exp)
      with expand-new-disjoint-synth {τ' = τ'} hn exp
    ... | ih = {!!}
    expand-new-disjoint-synth (HNHole x) ESEHole = {!!}
    expand-new-disjoint-synth (HNNEHole x hn) (ESNEHole x₁ exp) = {!!}
    expand-new-disjoint-synth (HNAp hn hn₁) (ESAp x x₁ x₂ x₃ x₄ x₅) = {!!}

    expand-new-disjoint-ana : ∀ { e u τ d Δ Γ τ' τ2} →
                              hole-name-new e u →
                              Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ → --too many τs?
                              Δ ## (■ (u , Γ , τ'))
    expand-new-disjoint-ana hn (EASubsume x x₁ x₂ x₃) = expand-new-disjoint-synth hn x₂
    expand-new-disjoint-ana (HNLam1 hn) (EALam x₁ x₂ ex) = {!!}
    expand-new-disjoint-ana (HNHole x) EAEHole = {!!}
    expand-new-disjoint-ana (HNNEHole x hn) (EANEHole x₁ x₂) = {!!}

  disjoint-union1 : {A : Set} {Γ1 Γ2 Δ : A ctx} → (Γ1 ∪ Γ2) ## Δ → Γ1 ## Δ
  disjoint-union1 {Γ1 = Γ1} {Γ2 = Γ2} {Δ = Δ} (ud1 , ud2) = du11 , du12
    where
      dom-union1 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → dom Γ1 n → dom (Γ1 ∪ Γ2) n
      dom-union1 Γ1 Γ2 n (π1 , π2) with Γ1 n
      dom-union1 Γ1 Γ2 n (π1 , π2) | Some x = x , refl
      dom-union1 Γ1 Γ2 n (π1 , ()) | None

      apart-union1 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → n # (Γ1 ∪ Γ2) → n # Γ1
      apart-union1 Γ1 Γ2 n aprt with Γ1 n
      apart-union1 Γ1 Γ2 n () | Some x
      apart-union1 Γ1 Γ2 n aprt | None = refl

      du11 : (n : Nat) → dom Γ1 n → n # Δ
      du11 n dom = ud1 n (dom-union1 Γ1 Γ2 n dom)

      du12 : (n : Nat) → dom Δ n → n # Γ1
      du12 n dom = apart-union1 Γ1 Γ2 n (ud2 n dom)

  disjoint-union2 : {A : Set} {Γ1 Γ2 Δ : A ctx} → (Γ1 ∪ Γ2) ## Δ → Γ2 ## Δ
  disjoint-union2 {Γ1 = Γ1} {Γ2 = Γ2} {Δ = Δ} (ud1 , ud2) = du21 , du22
    where
      dom-union2 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → dom Γ2 n → dom (Γ1 ∪ Γ2) n
      dom-union2 Γ1 Γ2 n (π1 , π2) with Γ1 n
      dom-union2 Γ3 Γ4 n (π1 , π2) | Some x = x , refl
      dom-union2 Γ3 Γ4 n (π1 , π2) | None = π1 , π2

      apart-union2 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → n # (Γ1 ∪ Γ2) → n # Γ2
      apart-union2 Γ1 Γ2 n aprt with Γ1 n
      apart-union2 Γ3 Γ4 n () | Some x
      apart-union2 Γ3 Γ4 n aprt | None = aprt

      du21 : (n : Nat) → dom Γ2 n → n # Δ
      du21 n dom = ud1 n (dom-union2 Γ1  Γ2 n dom)

      du22 : (n : Nat) → dom Δ n → n # Γ2
      du22 n dom = apart-union2 Γ1 Γ2 n (ud2 n dom)

  mutual
    expand-disjoint-new-synth : ∀{ e τ d Δ u Γ τ'} →
                                Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                                Δ ## (■ (u , Γ , τ')) →
                                hole-name-new e u
    expand-disjoint-new-synth ESConst disj = HNConst
    expand-disjoint-new-synth (ESVar x₁) disj = HNVar
    expand-disjoint-new-synth (ESLam x₁ ex) disj = HNLam2 (expand-disjoint-new-synth ex {!!})
    expand-disjoint-new-synth (ESAp {Δ1 = Δ1} x x₁ x₂ x₃ x₄ x₅) disj
      with expand-disjoint-new-ana x₄ (disjoint-union1 disj) | expand-disjoint-new-ana x₅ (disjoint-union2 {Γ1 = Δ1} disj)
    ... | ih1 | ih2 = HNAp ih1 ih2
    expand-disjoint-new-synth ESEHole disj = HNHole {!!}
    expand-disjoint-new-synth (ESNEHole x ex) disj = HNNEHole {!!} {!!}
    expand-disjoint-new-synth (ESAsc x) disj = HNAsc (expand-disjoint-new-ana x disj)

    expand-disjoint-new-ana : ∀{ e τ d Δ u Γ τ2 τ'} →
                                Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                                Δ ## (■ (u , Γ , τ')) →
                                hole-name-new e u
    expand-disjoint-new-ana (EALam x₁ x₂ ex) disj = HNLam1 (expand-disjoint-new-ana ex {!disj!})
    expand-disjoint-new-ana (EASubsume x x₁ x₂ x₃) disj = expand-disjoint-new-synth x₂ disj
    expand-disjoint-new-ana EAEHole disj = HNHole {!!}
    expand-disjoint-new-ana (EANEHole x x₁) disj = HNNEHole {!!} (expand-disjoint-new-synth x₁ {!!})

  disj3 : {A : Set} {Γ1 Γ2 Γ3 : A ctx} → Γ1 ## Γ3 → Γ2 ## Γ3 → (Γ1 ∪ Γ2) ## Γ3
  disj3 {_} {Γ1} {Γ2} {Γ3} D13 D23 = d31 , d32
    where
      dom-split : {A : Set} → (Γ1 Γ2 : A ctx) (n : Nat) → dom (Γ1 ∪ Γ2) n → dom Γ1 n + dom Γ2 n
      dom-split Γ4 Γ5 n (π1 , π2) with Γ4 n
      dom-split Γ4 Γ5 n (π1 , π2) | Some x = Inl (x , refl)
      dom-split Γ4 Γ5 n (π1 , π2) | None = Inr (π1 , π2)

      d31 : (n : Nat) → dom (Γ1 ∪ Γ2) n → n # Γ3
      d31 n D with dom-split Γ1 Γ2 n D
      d31 n D | Inl x = π1 D13 n x
      d31 n D | Inr x = π1 D23 n x

      union-parts : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → n # Γ1 → n # Γ2 → n # (Γ1 ∪ Γ2)
      union-parts Γ1 Γ2 n apt1 apt2 with Γ1 n
      union-parts _ _ n refl apt2 | .None = apt2

      d32 : (n : Nat) → dom Γ3 n → n # (Γ1 ∪ Γ2)
      d32 n D = union-parts Γ1 Γ2 n (π2 D13 n D) (π2 D23 n D)

  mutual
    -- this looks good but may not work because of the weakening calls
    expand-ana-disjoint : ∀{ e1 e2 τ1 τ2 e1' e2' τ1' τ2' Γ Δ1 Δ2 } →
          holes-disjoint e1 e2 →
          Γ ⊢ e1 ⇐ τ1 ~> e1' :: τ1' ⊣ Δ1 →
          Γ ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
          Δ1 ## Δ2
    expand-ana-disjoint hd (EASubsume x x₁ x₂ x₃) E2 = expand-synth-disjoint hd x₂ E2
    expand-ana-disjoint (HDLam1 hd) (EALam x₁ x₂ ex1) E2 = expand-ana-disjoint hd ex1 (weaken-ana-expand x₁ E2)
    expand-ana-disjoint (HDHole x) EAEHole E2 = ##-comm (expand-new-disjoint-ana x E2)
    expand-ana-disjoint (HDNEHole x hd) (EANEHole x₁ x₂) E2 = disj3 (expand-synth-disjoint hd x₂ E2) (##-comm (expand-new-disjoint-ana x E2))

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
    expand-synth-disjoint (HDNEHole x hd) (ESNEHole x₁ synth) ana = disj3 (expand-synth-disjoint hd synth ana) (##-comm (expand-new-disjoint-ana x ana))
    expand-synth-disjoint (HDAp hd hd₁) (ESAp x x₁ x₂ x₃ x₄ x₅) ana = disj3 (expand-ana-disjoint hd x₄ ana) (expand-ana-disjoint hd₁ x₅ ana)
