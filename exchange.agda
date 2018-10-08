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
  exchange-subst-Γ : ∀{Δ Γ x y τ1 τ2 σ Γ'} →
                   x ≠ y →
                   Δ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ σ :s: Γ' →
                   Δ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ σ :s: Γ'
  exchange-subst-Γ {Δ} {Γ} {x} {y} {τ1} {τ2} {σ} {Γ'} x≠y xy =
    tr (λ qq → Δ , qq ⊢ σ :s: Γ') (swap Γ x≠y) xy

  exchange-synth : ∀{Γ x y τ τ1 τ2 e}
                       → x ≠ y
                       → (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e => τ
                       → (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e => τ
  exchange-synth {Γ} {x} {y} {τ} {τ1} {τ2} {e} neq synth =
    tr (λ qq → qq ⊢ e => τ) (swap Γ neq) synth

  exchange-ana : ∀{Γ x y τ τ1 τ2 e}
                       → x ≠ y
                       → (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e <= τ
                       → (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e <= τ
  exchange-ana {Γ} {x} {y} {τ} {τ1} {τ2} {e} neq ana =
    tr (λ qq → qq ⊢ e <= τ) (swap Γ neq) ana
