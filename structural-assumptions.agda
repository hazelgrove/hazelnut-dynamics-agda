open import Prelude
open import Nat
open import core
open import contexts

module structural-assumptions where

-- this module contains postualtes that we intend to remove in the finished
-- artefact. they are all either canonical structural properties of the
-- hypothetical judgements or common properties of contexts. we strongly
-- believe that they are true, especially since they're all standard, but
-- have not yet proven them for our specific choices of implementations.

-- the only postulates not in this file are 1) for function
-- extensionality in Prelude.agda; funext is known to be independent
-- of Agda, and we have no intension of removing it, and 2) the
-- signature of the disjointness judgements in core.agda used below to
-- break a circular module dependency, and 3) the signature of
-- applying a substitition to a hole in core.agda


-- assumptions about contexts
postulate
  ∪comm : {A : Set} → (C1 C2 : A ctx) → C1 ## C2 → (C1 ∪ C2) == (C2 ∪ C1)
  x∈sing : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) → (n , a) ∈ (Γ ,, (n , a))
  x∈∪r : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) → (n , x) ∈ Γ' → Γ ## Γ' → (n , x) ∈ (Γ ∪ Γ') -- follows from comm?
  gcomp-extend : ∀{Γ τ x} → Γ gcomplete → τ tcomplete → (Γ ,, (x , τ)) gcomplete

postulate
  subst-weaken : ∀{Δ Γ Γ' Δ' σ} → Δ ## Δ' → Δ , Γ ⊢ σ :s: Γ' → (Δ ∪ Δ') , Γ ⊢ σ :s: Γ'

-- assumptions about disjointness (these need a new judgemental form
-- to generate two disjoint sets of hole names to prove)
postulate
  expand-ana-disjoint : ∀{ e1 e2 τ1 τ2 e1' e2' τ1' τ2' Γ Δ1 Δ2 } →
          holes-disjoint e1 e2 →
          Γ ⊢ e1 ⇐ τ1 ~> e1' :: τ1' ⊣ Δ1 →
          Γ ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
          Δ1 ## Δ2
  expand-new-disjoint : ∀ { e u τ d Δ Γ τ'} →
                        hole-name-new e u →
                        Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                        Δ ## (■ (u , Γ , τ'))
  expand-disjoint-new : ∀{ e τ d Δ u Γ τ'} →
                      Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                      Δ ## (■ (u , Γ , τ')) →
                      hole-name-new e u

-- structural properties of hypothetical judgements
postulate
  lem-weakenΔ1 : ∀{Δ1 Δ2 Γ d τ} → Δ1 ## Δ2 → Δ1 , Γ ⊢ d :: τ → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ

-- assumptions about substitution
postulate
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2 } →
              Δ , Γ ,, (x , τ1) ⊢ d1 :: τ →
              Δ , Γ ⊢ d2 :: τ1 →
              Δ , Γ ⊢ [ d2 / x ] d1 :: τ
