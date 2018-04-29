open import Prelude
open import Nat
open import core
open import contexts

open import structural

module disjointness where
  disjoint-parts : {A : Set} {Γ1 Γ2 Γ3 : A ctx} → Γ1 ## Γ3 → Γ2 ## Γ3 → (Γ1 ∪ Γ2) ## Γ3
  disjoint-parts {_} {Γ1} {Γ2} {Γ3} D13 D23 = d31 , d32
    where
      dom-split : {A : Set} → (Γ1 Γ2 : A ctx) (n : Nat) → dom (Γ1 ∪ Γ2) n → dom Γ1 n + dom Γ2 n
      dom-split Γ4 Γ5 n (π1 , π2) with Γ4 n
      dom-split Γ4 Γ5 n (π1 , π2) | Some x = Inl (x , refl)
      dom-split Γ4 Γ5 n (π1 , π2) | None = Inr (π1 , π2)

      d31 : (n : Nat) → dom (Γ1 ∪ Γ2) n → n # Γ3
      d31 n D with dom-split Γ1 Γ2 n D
      d31 n D | Inl x = π1 D13 n x
      d31 n D | Inr x = π1 D23 n x

      apart-parts : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) → n # Γ1 → n # Γ2 → n # (Γ1 ∪ Γ2)
      apart-parts Γ1 Γ2 n apt1 apt2 with Γ1 n
      apart-parts _ _ n refl apt2 | .None = apt2

      d32 : (n : Nat) → dom Γ3 n → n # (Γ1 ∪ Γ2)
      d32 n D = apart-parts Γ1 Γ2 n (π2 D13 n D) (π2 D23 n D)

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

  lem : {A : Set} (y : A) (n m : Nat) → dom (■ (m , y)) n → n == m
  lem y n m (π1 , π2) with natEQ m n
  lem y n .n (π1 , π2) | Inl refl = refl
  lem y n m (π1 , π2) | Inr x = abort (somenotnone (! π2))

  disjoint-singles : {A : Set} {x y : A} {u1 u2 : Nat} → u1 ≠ u2 → (■ (u1 , x)) ## (■ (u2 , y))
  disjoint-singles {_} {x} {y} {u1} {u2} neq = ds1 , ds2
    where
      ds1 : (n : Nat) → dom (■ (u1 , x)) n → n # (■ (u2 , y))
      ds1 n d with lem _ _ _ d
      ds1 .u1 d | refl with natEQ u2 u1
      ds1 .u1 d | refl | Inl xx = abort (neq (! xx))
      ds1 .u1 d | refl | Inr x₁ = refl

      ds2 : (n : Nat) → dom (■ (u2 , y)) n → n # (■ (u1 , x))
      ds2 n d with lem _ _ _ d
      ds2 .u2 d | refl with natEQ u1 u2
      ds2 .u2 d | refl | Inl x₁ = abort (neq x₁)
      ds2 .u2 d | refl | Inr x₁ = refl

  singles-notequal : {A : Set} {x y : A} {u1 u2 : Nat} → (■ (u1 , x)) ## (■ (u2 , y)) → u1 ≠ u2
  singles-notequal {A} {x} {y} {u1} {u2} (d1 , d2) = lemyy u1 u2 y (d1 u1 (lemxx u1 x))
    where
      lemxx : {A : Set} (p : Nat) (q : A) → dom (■ (p , q)) p
      lemxx p q with natEQ p p
      lemxx p q | Inl refl = q , refl
      lemxx p q | Inr x₁ = abort (x₁ refl)

      lemyy : {A : Set} (p r : Nat) (q : A) → p # (■ (r , q)) → p ≠ r
      lemyy p r q apt with natEQ r p
      lemyy p .p q apt | Inl refl = abort (somenotnone apt)
      lemyy p r q apt | Inr x₁ = flip x₁

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
