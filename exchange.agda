open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

module exchange where
  -- exchanging just two disequal elements produces the same context
  swap-little : {A : Set} {x y : Nat} {τ1 τ2 : A} → (x ≠ y) →
    ((■ (x , τ1)) ,, (y , τ2)) == ((■ (y , τ2)) ,, (x , τ1))
  swap-little {A} {x} {y} {τ1} {τ2} neq = ∪comm (■ (x , τ1))
                                                (■ (y , τ2))
                                                (disjoint-singles neq)

  -- really the core of all the exchange arguments: contexts with two
  -- disequal elements exchanged are the same. we reassociate the unions,
  -- swap as above, and then associate them back.
  --
  -- note that this is generic in the contents of the context. the proofs
  -- below show the exchange properties that we actually need in the
  -- various other proofs; the remaning exchange properties for both Δ and
  -- Γ positions for all the other hypothetical judgements are exactly in
  -- this pattern.
  swap : {A : Set} {x y : Nat} {τ1 τ2 : A} (Γ : A ctx) (x≠y : x == y → ⊥) →
         ((Γ ,, (x , τ1)) ,, (y , τ2)) == ((Γ ,, (y , τ2)) ,, (x , τ1))
  swap {A} {x} {y} {τ1} {τ2} Γ neq =
                        (∪assoc Γ (■ (x , τ1)) (■ (y , τ2)) (disjoint-singles neq) ) ·
                        (ap1 (λ qq → Γ ∪ qq) (swap-little neq) ·
                        ! (∪assoc Γ (■ (y , τ2)) (■ (x , τ1)) (disjoint-singles (flip neq))))

  -- the above exchange principle used via transport in the judgements we needed
  exchange-subst-Γ : ∀{Δ Γ x y τ1 τ2 σ Γ' Θ} →
                   x ≠ y →
                   Δ , Θ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ σ :s: Γ' →
                   Δ , Θ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ σ :s: Γ'
  exchange-subst-Γ {Δ} {Γ} {x} {y} {τ1} {τ2} {σ} {Γ'}{Θ} x≠y =
    tr (λ qq → Δ , Θ , qq ⊢ σ :s: Γ') (swap Γ x≠y)

  exchange-synth : ∀{Γ x y τ τ1 τ2 e Θ}
                       → x ≠ y
                       → Θ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e => τ
                       → Θ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e => τ
  exchange-synth {Γ} {x} {y} {τ} {τ1} {τ2} {e} {Θ} neq  =
    tr (λ qq → Θ , qq ⊢ e => τ) (swap Γ neq)

  exchange-ana : ∀{Γ x y τ τ1 τ2 e Θ}
                       → x ≠ y
                       → Θ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e <= τ
                       → Θ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e <= τ
  exchange-ana {Γ} {x} {y} {τ} {τ1} {τ2} {e} {Θ} neq  =
    tr (λ qq → Θ , qq ⊢ e <= τ) (swap Γ neq)

  exchange-elab-synth : ∀{Γ x y τ1 τ2 e τ d Δ Θ} →
                        x ≠ y →
                        Θ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e ⇒ τ ~> d ⊣ Δ →
                        Θ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e ⇒ τ ~> d ⊣ Δ
  exchange-elab-synth {Γ = Γ} {e = e} {τ = τ} {d = d } {Δ = Δ} {Θ} neq =
    tr (λ qq → Θ , qq ⊢ e ⇒ τ ~> d ⊣ Δ) (swap Γ neq)

  exchange-elab-ana : ∀ {Γ x y τ1 τ2 τ τ' d e Δ Θ} →
                      x ≠ y →
                      Θ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      Θ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
  exchange-elab-ana {Γ = Γ} {τ = τ} {τ' = τ'} {d = d} {e = e} {Δ = Δ} {Θ = Θ} neq =
    tr (λ qq → Θ , qq ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ) (swap Γ neq)

  exchange-ta-Γ : ∀{Γ x y τ1 τ2 d τ Δ Θ } →
                x ≠ y →
                Δ , Θ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ d :: τ →
                Δ , Θ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ d :: τ
  exchange-ta-Γ {Γ = Γ} {d = d} {τ = τ} {Δ = Δ} {Θ = Θ} neq =
    tr (λ qq → Δ , Θ , qq ⊢ d :: τ) (swap Γ neq)

  exchange-ta-Θ-weak : ∀{Γ x y d τ Δ Θ } →
                x ≠ y →
                Δ , (Θ ,, (x , <>) ,, (y , <>)) , Γ ⊢ d :: τ →
                Δ , (Θ ,, (y , <>) ,, (x , <>)) , Γ ⊢ d :: τ
  exchange-ta-Θ-weak {Γ = Γ} {d = d} {τ = τ} {Δ = Δ} {Θ = Θ} neq =
    tr (λ qq → Δ , qq , Γ ⊢ d :: τ) (swap Θ neq)

  exchange-wf-weak : ∀{x y τ Θ } →
                x ≠ y →
                (Θ ,, (x , <>) ,, (y , <>)) ⊢ τ wf →
                (Θ ,, (y , <>) ,, (x , <>)) ⊢ τ wf
  exchange-wf-weak {τ = τ} {Θ = Θ} neq =
    tr (λ qq → qq ⊢ τ wf) (swap Θ neq)

  -- In fact, we can make a stronger claim because the codomain is all Top
  exchange-Θ : ∀{x y Θ} → (Θ ,, (x , <>) ,, (y , <>)) == (Θ ,, (y , <>) ,, (x , <>))
  exchange-Θ {x} {y} {Θ = Θ} = foo
    where
      -- foo2 : (qq : Nat) -> (Θ ∪ ((■ (x , <>)) ∪ (■ (y , <>)))) qq == (Θ ∪ ((■ (y , <>)) ∪ (■ (x , <>)))) qq -> (Θ ,, (x , <>) ,, (y , <>)) qq == (Θ ,, (y , <>) ,, (x , <>)) qq
      -- foo2 qq = {!!}
      foo-assoc1 : x ≠ y -> ((Θ ∪ (■ (x , <>))) ∪ (■ (y , <>))) == (Θ ∪ ((■ (x , <>)) ∪ ■ (y , <>)))
      foo-assoc1 neq = ∪assoc Θ (■ (x , <>)) (■ (y , <>)) ((lem-apart-sing-disj (lem-singleton-apart neq)))
      foo-comm : x ≠ y -> (Θ ∪ ((■ (x , <>)) ∪ ■ (y , <>))) == (Θ ∪ ((■ (y , <>)) ∪ ■ (x , <>))) 
      foo-comm neq rewrite ∪comm ((■ (y , <>))) (■ (x , <>)) (lem-apart-sing-disj (lem-singleton-apart (flip neq))) = refl
      foo-assoc2 : x ≠ y -> (Θ ∪ ((■ (y , <>)) ∪ (■ (x , <>)))) == ((Θ ∪ (■ (y , <>))) ∪ ■ (x , <>)) 
      foo-assoc2 neq rewrite ∪assoc Θ (■ (y , <>)) (■ (x , <>)) ((lem-apart-sing-disj (lem-singleton-apart (flip neq)))) = refl
      foo-lemma : ∀{Θ x y} -> (Θ ,, (x , <>) ,, (y , <>)) == ((Θ ∪ (■ (x , <>))) ∪ (■ (y , <>)))
      foo-lemma {Θ} {x} {y} = refl
      foo : (Θ ,, (x , <>) ,, (y , <>)) == (Θ ,, (y , <>) ,, (x , <>))
      foo with natEQ x y 
      ... | Inl refl = refl
      ... | Inr neq 
            rewrite foo-lemma {Θ} {x} {y}
            rewrite foo-assoc1 neq
            rewrite foo-comm neq
            rewrite foo-assoc2 neq
            rewrite ! (foo-lemma {Θ} {y} {x})
            =  refl

  exchange-ta-Θ : ∀{Γ x y d τ Δ Θ } →
                Δ , (Θ ,, (x , <>) ,, (y , <>)) , Γ ⊢ d :: τ →
                Δ , (Θ ,, (y , <>) ,, (x , <>)) , Γ ⊢ d :: τ
  exchange-ta-Θ {x = x} {y = y} {Θ = Θ} p rewrite exchange-Θ {y} {x} {Θ} = p

  exchange-wf : ∀{x y τ Θ } →
                (Θ ,, (x , <>) ,, (y , <>)) ⊢ τ wf →
                (Θ ,, (y , <>) ,, (x , <>)) ⊢ τ wf
  exchange-wf {x} {y} {Θ = Θ} pf with natEQ x y
  ... | Inl refl = pf
  ... | Inr neq = exchange-wf-weak {x} {y} {Θ = Θ} neq pf
