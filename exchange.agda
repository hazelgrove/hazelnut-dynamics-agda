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
                   Δ , (Γ ,, (x , τ1) ,, (y , τ2)) , Θ ⊢ σ :s: Γ' →
                   Δ , (Γ ,, (y , τ2) ,, (x , τ1)) , Θ ⊢ σ :s: Γ'
  exchange-subst-Γ {Δ} {Γ} {x} {y} {τ1} {τ2} {σ} {Γ'}{Θ} x≠y =
    tr (λ qq → Δ , qq , Θ ⊢ σ :s: Γ') (swap Γ x≠y)

  exchange-synth : ∀{Γ x y τ τ1 τ2 e Θ}
                       → x ≠ y
                       → (Γ ,, (x , τ1) ,, (y , τ2)) , Θ ⊢ e => τ
                       → (Γ ,, (y , τ2) ,, (x , τ1)) , Θ ⊢ e => τ
  exchange-synth {Γ} {x} {y} {τ} {τ1} {τ2} {e} {Θ} neq  =
    tr (λ qq → qq , Θ ⊢ e => τ) (swap Γ neq)

  exchange-ana : ∀{Γ x y τ τ1 τ2 e Θ}
                       → x ≠ y
                       → (Γ ,, (x , τ1) ,, (y , τ2)) , Θ ⊢ e <= τ
                       → (Γ ,, (y , τ2) ,, (x , τ1)) , Θ ⊢ e <= τ
  exchange-ana {Γ} {x} {y} {τ} {τ1} {τ2} {e} {Θ} neq  =
    tr (λ qq → qq , Θ ⊢ e <= τ) (swap Γ neq)

  exchange-elab-synth : ∀{Γ x y τ1 τ2 e τ d Δ Θ} →
                        x ≠ y →
                        (Γ ,, (x , τ1) ,, (y , τ2)) , Θ ⊢ e ⇒ τ ~> d ⊣ Δ →
                        (Γ ,, (y , τ2) ,, (x , τ1)) , Θ ⊢ e ⇒ τ ~> d ⊣ Δ
  exchange-elab-synth {Γ = Γ} {e = e} {τ = τ} {d = d } {Δ = Δ} {Θ} neq =
    tr (λ qq → qq , Θ ⊢ e ⇒ τ ~> d ⊣ Δ) (swap Γ neq)

  exchange-elab-ana : ∀ {Γ x y τ1 τ2 τ τ' d e Δ Θ} →
                      x ≠ y →
                      (Γ ,, (x , τ1) ,, (y , τ2)) , Θ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      (Γ ,, (y , τ2) ,, (x , τ1)) , Θ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
  exchange-elab-ana {Γ = Γ} {τ = τ} {τ' = τ'} {d = d} {e = e} {Δ = Δ} {Θ = Θ} neq =
    tr (λ qq → qq , Θ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ) (swap Γ neq)

  exchange-ta-Γ : ∀{Γ x y τ1 τ2 d τ Δ Θ } →
                x ≠ y →
                Δ , (Γ ,, (x , τ1) ,, (y , τ2)) , Θ ⊢ d :: τ →
                Δ , (Γ ,, (y , τ2) ,, (x , τ1)) , Θ ⊢ d :: τ
  exchange-ta-Γ {Γ = Γ} {d = d} {τ = τ} {Δ = Δ} {Θ = Θ} neq =
    tr (λ qq → Δ , qq , Θ ⊢ d :: τ) (swap Γ neq)
